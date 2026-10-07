/**
 * @file src/serdes/type.cpp
 * @brief Data type (de)serialization.
 * @copyright (c) 2019 Avast Software, licensed under the MIT license
 */

#include <rapidjson/prettywriter.h>
#include <rapidjson/stringbuffer.h>

#include "retdec/common/type.h"
#include "retdec/serdes/type.h"
#include "retdec/serdes/std.h"

namespace {

const std::string JSON_llvmIr     = "llvmIr";
const std::string JSON_wideString = "isWideString";
const std::string JSON_volatile   = "isVolatile";

} // anonymous namespace

namespace retdec {
namespace serdes {

template <typename Writer>
void serialize(Writer& writer, const common::Type& t)
{
	writer.StartObject();

	serializeString(writer, JSON_llvmIr, t.getLlvmIr(), t.isDefined());
	serializeString(writer, "cType", t.getCType(), !t.getCType().empty());
	serializeBool(writer, JSON_volatile, t.isVolatile(), t.isDefined() && t.isVolatile());
	serializeBool(writer, JSON_wideString, t.isWideString(), t.isDefined() && t.isWideString());

	writer.EndObject();
}
SERIALIZE_EXPLICIT_INSTANTIATION(common::Type)

void deserialize(const rapidjson::Value& val, common::Type& t)
{
	if (val.IsNull() || !val.IsObject())
	{
		return;
	}

	t.setLlvmIr(deserializeString(val, JSON_llvmIr));
	t.setCType(deserializeString(val, "cType"));
	t.setIsVolatile(deserializeBool(val, JSON_volatile));
	t.setIsWideString(deserializeBool(val, JSON_wideString));
}

} // namespace serdes
} // namespace retdec
