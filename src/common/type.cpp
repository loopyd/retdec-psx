/**
 * @file src/common/type.cpp
 * @brief Common data type representation.
 * @copyright (c) 2017 Avast Software, licensed under the MIT license
 */

#include <algorithm>
#include <cassert>

#include "retdec/common/type.h"

namespace retdec {
namespace common {

namespace {

struct CBaseType
{
	const char* spelling;
	unsigned width;
	bool isUnsigned;
};

const CBaseType cBaseTypes[] = {
	{"char", 8, false},
	{"signed char", 8, false},
	{"unsigned char", 8, true},
	{"s8", 8, false},
	{"u8", 8, true},
	{"int8_t", 8, false},
	{"uint8_t", 8, true},
	{"short", 16, false},
	{"signed short", 16, false},
	{"unsigned short", 16, true},
	{"s16", 16, false},
	{"u16", 16, true},
	{"int16_t", 16, false},
	{"uint16_t", 16, true},
	{"int", 32, false},
	{"signed", 32, false},
	{"signed int", 32, false},
	{"unsigned", 32, true},
	{"unsigned int", 32, true},
	{"s32", 32, false},
	{"u32", 32, true},
	{"int32_t", 32, false},
	{"uint32_t", 32, true},
};

const CBaseType* findCBaseType(const std::string& spelling)
{
	std::string base = spelling.substr(0, spelling.find('*'));
	auto notSpace = [](char c) { return c != ' ' && c != '\t'; };
	base.erase(base.begin(), std::find_if(base.begin(), base.end(), notSpace));
	base.erase(std::find_if(base.rbegin(), base.rend(), notSpace).base(), base.end());

	for (const auto& candidate : cBaseTypes)
	{
		if (base == candidate.spelling)
		{
			return &candidate;
		}
	}
	return nullptr;
}

}

/**
 * Default type is i32.
 */
Type::Type()
{
}

Type::Type(const std::string& llvmIrRepre) :
		_llvmIr(llvmIrRepre)
{
}

/**
 * @return Type is defined if @c llvmIr member is not empty.
 */
bool Type::isDefined() const
{
	return !_llvmIr.empty();
}

/**
 * Wide strings are in LLVM IR represented as int arrays.
 * This flag can be use to distinguish them from ordinary int arrays.
 */
bool Type::isWideString() const
{
	return _wideString;
}

void Type::setIsWideString(bool b)
{
	_wideString = b;
}

void Type::setLlvmIr(const std::string& t)
{
	_llvmIr = t;
}

/**
 * @return Width in bits of the supplied C spelling's base type, or 0 when the
 *         spelling has no supported scalar base type.
 */
unsigned Type::getCBaseTypeWidth() const
{
	const CBaseType* base = findCBaseType(_cType);
	return base ? base->width : 0;
}

/**
 * @return True when the supplied C spelling's base type is unsigned.
 */
bool Type::hasUnsignedBaseType() const
{
	const CBaseType* base = findCBaseType(_cType);
	return base ? base->isUnsigned : false;
}

/**
 * @return Type's ID is its LLVM IR representation.
 */
std::string Type::getId() const
{
	return getLlvmIr();
}

/**
 * @return LLVM IR string representation (unique ID).
 */
std::string Type::getLlvmIr() const
{
	assert(isDefined());
	return _llvmIr;
}

/**
 * Less-than comparison of this instance with the provided one.
 * Default string comparison of @c llvmIr members is used.
 * @param val Other type to compare with.
 * @return True if @c this instance is considered to be less-than @c val.
 */
bool Type::operator<(const Type& val) const
{
	assert(isDefined());
	return getLlvmIr() < val.getLlvmIr();
}

/**
 * Types are equal if their llvm ir representations are equal.
 */
bool Type::operator==(const Type& val) const
{
	assert(isDefined());
	return getLlvmIr() == val.getLlvmIr();
}

} // namespace common
} // namespace retdec
