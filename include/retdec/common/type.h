/**
 * @file include/retdec/common/type.h
 * @brief Common data type representation.
 * @copyright (c) 2019 Avast Software, licensed under the MIT license
 */

#ifndef RETDEC_COMMON_TYPE_H
#define RETDEC_COMMON_TYPE_H

#include <set>
#include <string>

namespace retdec {
namespace common {

/**
 * Represents data type.
 *
 * Type's LLVM IR representation is its unique ID.
 */
class Type
{
	public:
		Type();
		Type(const std::string& llvmIrRepre);

		/// @name Type query methods.
		/// @{
		bool isDefined() const;
		bool isWideString() const;
		/// @}

		/// @name Type set methods.
		/// @{
		void setLlvmIr(const std::string& t);
		void setIsWideString(bool b);
		void setCType(const std::string& t) { _cType = t; }
		const std::string& getCType() const { return _cType; }
		void setIsVolatile(bool b) { _volatile = b; }
		bool isVolatile() const { return _volatile; }
		/// @}

		/// @name Supplied source spelling queries.
		///
		/// The C spelling can carry information the signless LLVM/register type
		/// cannot, e.g. the signedness of the base type. Only scalar integer base
		/// spellings are supported.
		/// @{
		/// Width in bits of the spelling's base type, or 0 when unsupported.
		unsigned getCBaseTypeWidth() const;
		/// True when the spelling's base type is unsigned.
		bool hasUnsignedBaseType() const;
		/// @}

		/// @name Type get methods.
		/// @{
		std::string getId() const;
		std::string getLlvmIr() const;
		/// @}

		bool operator<(const Type& val) const;
		bool operator==(const Type& val) const;

	private:
		/// LLVM IR string representation.
		/// Unique ID.
		std::string _llvmIr = "i32";
		std::string _cType;
		bool _volatile = false;
		/// Wide strings are in LLVM IR represented as int arrays.
		/// This flag can be use to distinguish them from ordinary int arrays.
		bool _wideString = false;
};

using TypeContainer = std::set<Type>;

} // namespace common
} // namespace retdec

#endif
