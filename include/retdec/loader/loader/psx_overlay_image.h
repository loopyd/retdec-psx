#ifndef RETDEC_LOADER_PSX_OVERLAY_IMAGE_H
#define RETDEC_LOADER_PSX_OVERLAY_IMAGE_H

#include "retdec/common/psx_memory.h"
#include "retdec/loader/loader/image.h"

namespace retdec { namespace loader {

std::vector<common::PsxOriginalImage> readPsxImageMetadata(const std::string& path, const std::string& expectedHash = {});

common::PsxOriginalImage readPsxCopiedOriginal(const std::string& path, const std::string& expectedHash = {});

struct PsxOverlayOperation {
	enum class Kind { Mount, Dismount };
	Kind kind;
	std::string imageId;
	std::optional<common::PsxOriginalImage> image;
};

class PsxOverlayManager {
public:
	PsxOverlayManager();
	std::shared_ptr<const common::PsxMemoryContext> apply(const std::vector<PsxOverlayOperation>& operations);
	std::shared_ptr<const common::PsxMemoryContext> snapshot() const { return _snapshot; }
private:
	std::shared_ptr<const common::PsxMemoryContext> _snapshot;
};

class PsxOverlayImage final : public Image {
public:
	PsxOverlayImage(std::shared_ptr<fileformat::FileFormat> root,
		std::shared_ptr<const common::PsxMemoryContext> context);
	bool load() override;
private:
	std::shared_ptr<const common::PsxMemoryContext> _context;
	std::vector<std::shared_ptr<fileformat::FileFormat>> _formats;
};

} }

#endif
