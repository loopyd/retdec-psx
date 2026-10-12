#include "retdec/loader/loader/psx_overlay_image.h"

#include <array>
#include <cerrno>
#include <fcntl.h>
#include <map>
#include <set>
#include <stdexcept>
#include <sys/stat.h>
#include <unistd.h>
#include <rapidjson/document.h>
#include <rapidjson/stringbuffer.h>
#include <rapidjson/writer.h>
#include "retdec/fileformat/file_format/raw_data/raw_data_format.h"
#include "retdec/fileformat/utils/crypto.h"

namespace retdec { namespace loader {
namespace {

constexpr uint64_t ImageLimit = 16 << 20;
constexpr uint64_t TotalLimit = 64 << 20;
constexpr size_t MountLimit = 128;

void require(bool value, const char* error) {
	if (!value) throw std::runtime_error(error);
}

std::vector<uint8_t> readFile(const std::string& path, uint64_t limit) {
	require(!path.empty() && path.front() == '/', "psx-image-path-must-be-absolute");
	int fd = open(path.c_str(), O_RDONLY | O_CLOEXEC | O_NOFOLLOW);
	require(fd >= 0, "psx-image-open-failed");
	struct Close { int fd; ~Close() { close(fd); } } closeFile{fd};
	struct stat info;
	require(fstat(fd, &info) == 0 && S_ISREG(info.st_mode) && info.st_size >= 0
		&& uint64_t(info.st_size) <= limit, "psx-image-file-bound");
	std::vector<uint8_t> bytes(size_t(info.st_size));
	size_t offset = 0;
	while (offset < bytes.size()) {
		auto count = read(fd, bytes.data() + offset, bytes.size() - offset);
		if (count < 0 && errno == EINTR) continue;
		require(count > 0, "psx-image-read-failed");
		offset += size_t(count);
	}
	uint8_t extra;
	require(read(fd, &extra, 1) == 0, "psx-image-file-changed");
	return bytes;
}

std::string hash(const std::vector<uint8_t>& bytes) {
	return fileformat::getSha256(bytes.data(), bytes.size());
}

rapidjson::Document document(const std::vector<uint8_t>& bytes) {
	rapidjson::Document doc;
	doc.Parse<rapidjson::kParseFullPrecisionFlag | rapidjson::kParseIterativeFlag>(
		reinterpret_cast<const char*>(bytes.data()), bytes.size());
	require(!doc.HasParseError() && doc.IsObject(), "psx-metadata-json-invalid");
	return doc;
}

std::string text(const rapidjson::Value& row, const char* key) {
	require(row.IsObject() && row.HasMember(key) && row[key].IsString(), "psx-metadata-string-invalid");
	std::string result(row[key].GetString(), row[key].GetStringLength());
	require(!result.empty() && result.size() <= 4096 && result.find('\0') == std::string::npos,
		"psx-metadata-string-bound");
	return result;
}

uint64_t number(const rapidjson::Value& row, const char* key) {
	require(row.IsObject() && row.HasMember(key) && row[key].IsUint64(), "psx-metadata-number-invalid");
	return row[key].GetUint64();
}

bool digest(const std::string& value) {
	return value.size() == 64 && std::all_of(value.begin(), value.end(), [](char c) {
		return (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f');
	});
}

common::PsxOriginalImage imageMetadata(const rapidjson::Value& row) {
	common::PsxOriginalImage image;
	image.id = text(row, "image_id"); image.fileHash = text(row, "file_sha256");
	image.payloadHash = text(row, "payload_sha256"); image.fileBytes = number(row, "file_bytes");
	image.payloadOffset = number(row, "payload_offset"); image.payloadBytes = number(row, "payload_bytes");
	image.loadAddress = number(row, "load_address");
	return image;
}

bool sameMapping(const common::PsxOriginalImage& a, const common::PsxOriginalImage& b) {
	return a.id == b.id && a.fileHash == b.fileHash && a.payloadHash == b.payloadHash
		&& a.fileBytes == b.fileBytes && a.payloadOffset == b.payloadOffset
		&& a.payloadBytes == b.payloadBytes && a.loadAddress == b.loadAddress;
}

uint32_t word(const std::vector<uint8_t>& bytes, size_t offset) {
	return uint32_t(bytes[offset]) | uint32_t(bytes[offset + 1]) << 8
		| uint32_t(bytes[offset + 2]) << 16 | uint32_t(bytes[offset + 3]) << 24;
}

common::PsxOriginalImage validateImage(common::PsxOriginalImage image) {
	require(digest(image.fileHash) && digest(image.payloadHash) && image.fileBytes <= ImageLimit
		&& image.payloadBytes > 0 && image.payloadOffset <= image.fileBytes
		&& image.payloadBytes <= image.fileBytes - image.payloadOffset, "psx-image-extent-invalid");
	auto canonical = common::psxRamAddress(image.loadAddress);
	require(canonical && image.loadAddress % 4 == 0 && image.payloadBytes <= 0x80200000 - *canonical,
		"psx-image-ram-mapping-invalid");
	auto bytes = readFile(image.filePath, ImageLimit);
	require(bytes.size() == image.fileBytes && hash(bytes) == image.fileHash, "psx-image-file-identity-differs");
	if (image.mappingKind == "psx-exe-header") {
		require(bytes.size() >= 0x800 && std::equal(bytes.begin(), bytes.begin() + 8, "PS-X EXE")
			&& image.payloadOffset == 0x800 && word(bytes, 0x18) == image.loadAddress
			&& word(bytes, 0x1c) == image.payloadBytes, "psx-executable-load-evidence-differs");
		image.mappingPath = image.filePath; image.mappingHash = image.fileHash;
	} else {
		require(image.mappingKind == "original-catalog" && digest(image.mappingHash), "psx-image-load-evidence-required");
		auto mapping = readFile(image.mappingPath, 1 << 20);
		require(hash(mapping) == image.mappingHash, "psx-image-load-evidence-identity-differs");
		auto doc = document(mapping);
		require(text(doc, "schema") == "retdec118.original-image-catalog/v1"
			&& doc.HasMember("images") && doc["images"].IsArray() && doc["images"].Size() <= MountLimit,
			"psx-image-load-catalog-invalid");
		unsigned matches = 0;
		for (const auto& row : doc["images"].GetArray())
			if (sameMapping(image, imageMetadata(row))) ++matches;
		require(matches == 1, "psx-image-load-catalog-mapping-differs");
	}
	auto payload = std::make_shared<std::vector<uint8_t>>(bytes.begin() + image.payloadOffset,
		bytes.begin() + image.payloadOffset + image.payloadBytes);
	require(hash(*payload) == image.payloadHash, "psx-image-payload-identity-differs");
	image.payload = std::move(payload);
	return image;
}

std::vector<common::PsxVisibleInterval> visible(const std::vector<common::PsxOriginalImage>& mounts) {
	std::set<uint64_t> boundaries;
	for (const auto& image : mounts) {
		auto start = *common::psxRamAddress(image.loadAddress);
		boundaries.insert(start); boundaries.insert(start + image.payloadBytes);
	}
	std::vector<common::PsxVisibleInterval> intervals;
	for (auto it = boundaries.begin(); it != boundaries.end(); ++it) {
		auto next = std::next(it);
		if (next == boundaries.end()) break;
		for (size_t i = mounts.size(); i > 0; --i) {
			auto start = *common::psxRamAddress(mounts[i - 1].loadAddress);
			if (*it < start || *it >= start + mounts[i - 1].payloadBytes) continue;
			if (!intervals.empty() && intervals.back().imageIndex == i - 1 && intervals.back().end == *it)
				intervals.back().end = *next;
			else intervals.push_back({*it, *next, *it - start, i - 1});
			break;
		}
	}
	return intervals;
}

}

std::vector<common::PsxOriginalImage> readPsxImageMetadata(const std::string& path) {
	auto bytes = readFile(path, 1 << 20);
	auto doc = document(bytes);
	auto schema = text(doc, "schema");
	bool catalog = schema == "retdec118.original-image-catalog/v1";
	require(catalog || schema == "psx.overlay-images/v1", "psx-overlay-metadata-schema-invalid");
	require(doc.HasMember("images") && doc["images"].IsArray() && !doc["images"].Empty()
		&& doc["images"].Size() <= MountLimit, "psx-overlay-image-count-bound");
	std::vector<common::PsxOriginalImage> result;
	std::set<std::string> ids;
	auto directory = path.substr(0, path.find_last_of('/'));
	for (const auto& row : doc["images"].GetArray()) {
		auto image = imageMetadata(row);
		require(ids.insert(image.id).second, "psx-overlay-image-id-duplicate");
		if (catalog) {
			auto index = number(row, "payload_index");
			require(index < MountLimit, "psx-overlay-payload-index-bound");
			auto digits = std::to_string(index);
			image.filePath = directory + "/images/" + std::string(3 - digits.size(), '0') + digits + ".image";
			image.mappingKind = "original-catalog"; image.mappingPath = path; image.mappingHash = hash(bytes);
			require(doc.HasMember("targets") && doc["targets"].IsArray(), "psx-overlay-catalog-targets-invalid");
			for (const auto& target : doc["targets"].GetArray())
				if (text(target, "image_id") == image.id) {
					if (image.target.empty()) image.target = text(target, "target");
					else image.target = image.id;
				}
		} else {
			image.target = text(row, "target"); image.filePath = text(row, "file_path");
			image.mappingKind = text(row, "mapping_kind");
			if (image.mappingKind != "psx-exe-header") {
				image.mappingPath = text(row, "mapping_path"); image.mappingHash = text(row, "mapping_sha256");
			}
		}
		require(!image.target.empty(), "psx-overlay-target-missing");
		result.push_back(std::move(image));
	}
	return result;
}

PsxOverlayManager::PsxOverlayManager() { apply({}); }

std::shared_ptr<const common::PsxMemoryContext> PsxOverlayManager::apply(const std::vector<PsxOverlayOperation>& operations) {
	require(operations.size() <= MountLimit * 2, "psx-overlay-operation-count-bound");
	auto candidate = std::make_shared<common::PsxMemoryContext>();
	if (_snapshot) candidate->_mounts = _snapshot->mounts();
	for (const auto& operation : operations) {
		auto& mounts = candidate->_mounts;
		auto found = std::find_if(mounts.begin(), mounts.end(), [&](const auto& image) { return image.id == operation.imageId; });
		if (operation.kind == PsxOverlayOperation::Kind::Dismount) {
			if (found != mounts.end()) mounts.erase(found);
			continue;
		}
		require(operation.image && operation.image->id == operation.imageId, "psx-overlay-mount-metadata-missing");
		if (found == mounts.end()) {
			uint64_t total = 0;
			for (const auto& image : mounts) total += image.payloadBytes;
			require(mounts.size() < MountLimit, "psx-overlay-mount-count-bound");
			require(operation.image->payloadBytes <= TotalLimit - total, "psx-overlay-aggregate-byte-bound");
		}
		auto image = validateImage(*operation.image);
		if (found != mounts.end()) {
			require(sameMapping(*found, image) && found->target == image.target, "psx-overlay-mounted-identity-differs");
			continue;
		}
		mounts.push_back(std::move(image));
	}
	uint64_t total = 0;
	for (const auto& image : candidate->_mounts) {
		require(image.payloadBytes <= TotalLimit - total, "psx-overlay-aggregate-byte-bound");
		total += image.payloadBytes;
	}
	candidate->_intervals = visible(candidate->_mounts);
	rapidjson::StringBuffer buffer;
	rapidjson::Writer<rapidjson::StringBuffer> writer(buffer);
	candidate->serialize(writer);
	candidate->_identity = fileformat::getSha256(reinterpret_cast<const unsigned char*>(buffer.GetString()), buffer.GetSize());
	if (_snapshot && _snapshot->identity() == candidate->identity()) return _snapshot;
	_snapshot = std::move(candidate);
	return _snapshot;
}

PsxOverlayImage::PsxOverlayImage(std::shared_ptr<fileformat::FileFormat> root,
	std::shared_ptr<const common::PsxMemoryContext> context) : Image(root), _context(std::move(context)) {}

bool PsxOverlayImage::load() {
	if (!_context || getNumberOfSegments()) return false;
	for (const auto& image : _context->mounts()) {
		auto format = std::make_shared<fileformat::RawDataFormat>(image.payload->data(), image.payload->size());
		format->initArchitecture(fileformat::Architecture::MIPS, utils::Endianness::LITTLE, 4,
			common::Address::Undefined, common::Address(*common::psxRamAddress(image.loadAddress)));
		auto* section = format->getSections().front();
		section->setName(image.id); section->setType(fileformat::Section::Type::CODE);
		_formats.push_back(std::move(format));
	}
	for (const auto& interval : _context->intervals()) {
		const auto& image = _context->mounts()[interval.imageIndex];
		for (uint64_t alias : {uint64_t(0), uint64_t(0x80000000), uint64_t(0xa0000000)}) {
			auto source = std::make_unique<SegmentDataSource>(llvm::StringRef(
				reinterpret_cast<const char*>(image.payload->data() + interval.payloadOffset), interval.end - interval.start), true);
			auto segment = std::make_unique<Segment>(_formats[interval.imageIndex]->getSections().front(),
				(interval.start & 0x1fffffff) | alias, interval.end - interval.start, std::move(source));
			segment->setName(image.id); insertSegment(std::move(segment));
		}
	}
	sortSegments();
	return getNumberOfSegments() > 0;
}

} }
