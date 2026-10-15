#ifndef RETDEC_COMMON_PSX_MEMORY_H
#define RETDEC_COMMON_PSX_MEMORY_H

#include <algorithm>
#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <vector>

namespace retdec { namespace loader { class PsxOverlayManager; } }

namespace retdec { namespace common {

struct PsxOriginalImage {
	std::string id, target, filePath, fileHash, payloadHash;
	std::string mappingKind, mappingPath, mappingHash;
	uint64_t fileBytes = 0, payloadOffset = 0, payloadBytes = 0, loadAddress = 0;
	std::optional<uint64_t> observedInstructionEntry;
	std::shared_ptr<const std::vector<uint8_t>> payload;
};

struct PsxVisibleInterval {
	uint64_t start, end, payloadOffset;
	size_t imageIndex;
};

inline std::optional<uint64_t> psxRamAddress(uint64_t address)
{
	if (address > UINT32_MAX) return {};
	auto region = address & 0xe0000000;
	if (region != 0 && region != 0x80000000 && region != 0xa0000000) return {};
	auto physical = address & 0x1fffffff;
	if (physical >= 0x200000) return {};
	return physical | 0x80000000;
}

class PsxMemoryContext {
public:
	struct ByteSpan {
		const PsxOriginalImage* image;
		const uint8_t* bytes;
		uint64_t payloadOffset, size;
	};

	const std::string& identity() const { return _identity; }
	const std::string& instructionScopeHash() const { return _instructionScopeHash; }
	const std::optional<uint64_t>& observedInstructionEntry() const { return _observedInstructionEntry; }
	const std::vector<PsxOriginalImage>& mounts() const { return _mounts; }
	const std::vector<PsxVisibleInterval>& intervals() const { return _intervals; }
	std::optional<ByteSpan> resolve(uint64_t address, uint64_t count) const {
		auto canonical = psxRamAddress(address);
		if (!canonical || !count || count > 0x80200000 - *canonical) return {};
		for (const auto& interval : _intervals) {
			if (*canonical < interval.start || *canonical >= interval.end) continue;
			if (count > interval.end - *canonical) return {};
			const auto& image = _mounts[interval.imageIndex];
			auto offset = interval.payloadOffset + *canonical - interval.start;
			return ByteSpan{&image, image.payload->data() + offset, offset, count};
		}
		return {};
	}

	template<typename Writer> void serialize(Writer& writer) const {
		writer.StartObject(); writer.Key("schema"); writer.String("psx.memory-context/v1");
		writer.Key("identity_sha256"); writer.String(_identity);
		if (!_instructionScopeHash.empty()) {
			writer.Key("instruction_scope_sha256"); writer.String(_instructionScopeHash);
		}
		writer.Key("mounts"); writer.StartArray();
		for (const auto& image : _mounts) {
			writer.StartObject();
			writer.Key("image_id"); writer.String(image.id); writer.Key("target"); writer.String(image.target);
			writer.Key("file_path"); writer.String(image.filePath); writer.Key("file_sha256"); writer.String(image.fileHash);
			writer.Key("file_bytes"); writer.Uint64(image.fileBytes); writer.Key("payload_offset"); writer.Uint64(image.payloadOffset);
			writer.Key("payload_sha256"); writer.String(image.payloadHash); writer.Key("payload_bytes"); writer.Uint64(image.payloadBytes);
			writer.Key("load_address"); writer.Uint64(image.loadAddress);
			writer.Key("mapping_kind"); writer.String(image.mappingKind); writer.Key("mapping_path"); writer.String(image.mappingPath);
			writer.Key("mapping_sha256"); writer.String(image.mappingHash); writer.EndObject();
		}
		writer.EndArray(); writer.Key("visible_intervals"); writer.StartArray();
		for (const auto& interval : _intervals) {
			writer.StartObject(); writer.Key("start"); writer.Uint64(interval.start); writer.Key("end"); writer.Uint64(interval.end);
			writer.Key("image_id"); writer.String(_mounts[interval.imageIndex].id);
			writer.Key("payload_offset"); writer.Uint64(interval.payloadOffset); writer.EndObject();
		}
		writer.EndArray(); writer.EndObject();
	}

private:
	friend class retdec::loader::PsxOverlayManager;
	std::string _identity, _instructionScopeHash;
	std::optional<uint64_t> _observedInstructionEntry;
	std::vector<PsxOriginalImage> _mounts;
	std::vector<PsxVisibleInterval> _intervals;
};

} }

#endif
