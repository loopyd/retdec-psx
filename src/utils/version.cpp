/**
 * @file src/utils/version.cpp
 * @brief RetDec version implementation.
 * @copyright (c) 2021 Avast Software, licensed under the MIT license
 */

#include "retdec/utils/version.h"

namespace retdec {
namespace utils {
namespace version {

std::string getCommitHash()
{
	return RETDEC_GIT_COMMIT_HASH;
}

std::string getShortCommitHash(unsigned length)
{
	return getCommitHash().substr(0, length);
}

std::string getBuildDate()
{
	return RETDEC_BUILD_DATE;
}

std::string getVersionTag()
{
	return RETDEC_GIT_VERSION_TAG;
}

std::string getVersionStringLong()
{
	return  "retdec-psx " RETDEC_VERSION "\n"
			"Commit hash    :  " + getCommitHash() + "\n"
			"Build date     :  " + getBuildDate();
}

std::string getVersionStringShort()
{
	return  "retdec-psx " RETDEC_VERSION "@" + getShortCommitHash() +
			" built on " + getBuildDate();
}

} // namespace version
} // namespace utils
} // namespace retdec
