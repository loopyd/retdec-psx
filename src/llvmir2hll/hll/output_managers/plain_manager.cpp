/**
* @file src/llvmir2hll/hll/output_managers/plain_manager.cpp
* @brief Implementation of PlainOutputManager.
* @copyright (c) 2019 Avast Software, licensed under the MIT license
*/

#include "retdec/llvmir2hll/hll/output_managers/plain_manager.h"
#include "retdec/utils/string.h"

namespace retdec {
namespace llvmir2hll {

PlainOutputManager::PlainOutputManager(llvm::raw_ostream& out) :
		_out(out)
{

}

void PlainOutputManager::finalize()
{
	finishCommentModifier();
}

void PlainOutputManager::newLine()
{
	finishCommentModifier();
	_out << "\n";
}

void PlainOutputManager::space(const std::string& space)
{
	writeFragment(space);
}

void PlainOutputManager::punctuation(char p)
{
	writeFragment(std::string(1, p));
}

void PlainOutputManager::operatorX(const std::string& op)
{
	writeFragment(op);
}

void PlainOutputManager::globalVariableId(const std::string& id)
{
	writeFragment(id);
}

void PlainOutputManager::localVariableId(const std::string& id)
{
	writeFragment(id);
}

void PlainOutputManager::memberId(const std::string& id)
{
	writeFragment(id);
}

void PlainOutputManager::labelId(const std::string& id)
{
	writeFragment(id);
}

void PlainOutputManager::functionId(const std::string& id)
{
	writeFragment(id);
}

void PlainOutputManager::parameterId(const std::string& id)
{
	writeFragment(id);
}

void PlainOutputManager::keyword(const std::string& k)

{
	writeFragment(k);
}

void PlainOutputManager::dataType(const std::string& t)
{
	writeFragment(t);
}

void PlainOutputManager::preprocessor(const std::string& p)
{
	writeFragment(p);
}

void PlainOutputManager::include(const std::string& i)
{
	writeFragment("<" + i + ">");
}

void PlainOutputManager::constantBool(const std::string& c)
{
	writeFragment(c);
}

void PlainOutputManager::constantInt(const std::string& c)
{
	writeFragment(c);
}

void PlainOutputManager::constantFloat(const std::string& c)
{
	writeFragment(c);
}

void PlainOutputManager::constantString(const std::string& c)
{
	writeFragment(c);
}

void PlainOutputManager::constantSymbol(const std::string& c)
{
	writeFragment(c);
}

void PlainOutputManager::constantPointer(const std::string& c)
{
	writeFragment(c);
}

void PlainOutputManager::comment(const std::string& c)
{
	if (_commentModifierOn)
	{
		_runningComment += " " + c;
		return;
	}
	_out << renderComment(c);
}

void PlainOutputManager::commentModifier()
{
	if (_commentModifierOn)
	{
		return;
	}
	if (getOutputLanguage() == "C")
	{
		_commentModifierOn = true;
		return;
	}
	_out << getCommentPrefix() << " ";
}

void PlainOutputManager::writeFragment(const std::string& text)
{
	if (_commentModifierOn)
	{
		_runningComment += text;
	}
	else
	{
		_out << text;
	}
}

void PlainOutputManager::finishCommentModifier()
{
	if (_commentModifierOn)
	{
		_out << renderComment(_runningComment);
		_commentModifierOn = false;
		_runningComment.clear();
	}
}

void PlainOutputManager::addressPush(Address a)
{
	// nothing
}

void PlainOutputManager::addressPop()
{
	// nothing
}

} // namespace llvmir2hll
} // namespace retdec
