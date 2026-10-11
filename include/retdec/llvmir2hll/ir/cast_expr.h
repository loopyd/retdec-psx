/**
* @file include/retdec/llvmir2hll/ir/cast_expr.h
* @brief Base class for cast instructions.
* @copyright (c) 2017 Avast Software, licensed under the MIT license
*/

#ifndef RETDEC_LLVMIR2HLL_IR_CAST_EXPR_H
#define RETDEC_LLVMIR2HLL_IR_CAST_EXPR_H

#include "retdec/llvmir2hll/ir/expression.h"
#include "retdec/common/function.h"
#include "retdec/llvmir2hll/ir/type.h"
#include "retdec/llvmir2hll/support/smart_ptr.h"

namespace retdec {
namespace llvmir2hll {

class Expression;
class Visitor;
class Variable;
class LLVMValueConverter;
class LLVMInstructionConverter;

class OriginalExtraction final {
public:
	const common::OriginalSourceExpression& witness() const { return original; }
	common::OriginalSourceForm form() const { return selectedForm; }
	const std::string& functionInitialName() const { return owner; }
	unsigned formalOrdinal() const { return ordinal; }
	ShPtr<Variable> parameter() const { return entryParameter; }

private:
	friend class LLVMValueConverter;
	OriginalExtraction(common::OriginalSourceExpression witness, common::OriginalSourceForm form,
		std::string functionInitialName, unsigned formalOrdinal, ShPtr<Variable> parameter):
		original(witness), selectedForm(form), owner(std::move(functionInitialName)),
		ordinal(formalOrdinal), entryParameter(parameter) {}
	const common::OriginalSourceExpression original;
	const common::OriginalSourceForm selectedForm;
	const std::string owner;
	const unsigned ordinal;
	const ShPtr<Variable> entryParameter;
};

using Extraction = std::shared_ptr<const OriginalExtraction>;

/**
* @brief Base class for cast instructions.
*
* Instances of this class have reference object semantics.
*/
class CastExpr: public Expression {
public:
	virtual ShPtr<Type> getType() const override;
	virtual void replace(ShPtr<Expression> oldExpr,
		ShPtr<Expression> newExpr) override;

	void setOperand(ShPtr<Expression> newOp);
	ShPtr<Expression> getOperand() const;
	Extraction getOriginalExtraction() const { return extraction; }

	/// @name Observer Interface
	/// @{
	virtual void update(ShPtr<Value> subject,
		ShPtr<Value> arg = nullptr) override;
	/// @}

protected:
	CastExpr(ShPtr<Expression> op, ShPtr<Type> dstType);
	void copyOriginalExtractionTo(CastExpr& clone) const { clone.extraction = extraction; }
	bool hasSameOriginalExtraction(const CastExpr& other) const { return extraction == other.extraction; }

private:
	friend class LLVMInstructionConverter;
	void setOriginalExtraction(Extraction association) { extraction = std::move(association); }
	Extraction extraction;

protected:
	/// Operand.
	ShPtr<Expression> op;

	/// Destination type.
	ShPtr<Type> dstType;
};

} // namespace llvmir2hll
} // namespace retdec

#endif
