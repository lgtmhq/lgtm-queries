// Copyright 2016 Semmle Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under
// the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
// KIND, either express or implied. See the License for the specific language governing
// permissions and limitations under the License.

/**
 * Classes for working with JSON data.
 */

import AST

/**
 * A JSON-encoded value, which may be a primitive value, an array or an object.
 */
class JSONValue extends @json_value, Locatable {
  /** Get the parent value to which this value belongs, if any. */
  JSONValue getParent() {
    json(this, _, result, _, _)
  }

  /** Get the i-th child value of this value, if any. */
  JSONValue getChild(int i) {
    json(result, _, this, i, _)
  }

  /** Is this JSON value the top level element in its enclosing file? */
  predicate isTopLevel() {
    not exists(getParent())
  }

  string toString() {
    json(this, _, _, _, result)
  }
}

/**
 * A JSON-encoded primitive value.
 */
abstract class JSONPrimitiveValue extends JSONValue {
  /** Get a string representation of the encoded value. */
  string getValue() {
    json_literals(result, _, this)
  }

  /** Get the source text of the encoded value; for strings, this includes quotes. */
  string getRawValue() {
    json_literals(_, result, this)
  }
}

/**
 * A JSON-encoded null value.
 */
class JSONNull extends @json_null, JSONPrimitiveValue {
}

/**
 * A JSON-encoded Boolean value.
 */
class JSONBoolean extends @json_boolean, JSONPrimitiveValue {
}

/**
 * A JSON-encoded number.
 */
class JSONNumber extends @json_number, JSONPrimitiveValue {
}

/**
 * A JSON-encoded string value.
 */
class JSONString extends @json_string, JSONPrimitiveValue {
}

/**
 * A JSON-encoded array.
 */
class JSONArray extends @json_array, JSONValue {
  /** Get the value of the i-th element of this array. */
  JSONValue getElementValue(int i) {
    result = getChild(i)
  }

  /** Get the string value of the i-th element of this array. */
  string getElementStringValue(int i) {
    result = ((JSONString)getElementValue(i)).getValue()
  }
}

/**
 * A JSON-encoded object.
 */
class JSONObject extends @json_object, JSONValue {
  /** Get the value of property <code>name</code>. */
  JSONValue getPropValue(string name) {
    json_properties(this, name, result)
  }

  /** Get the string value of the property <code>name</code>. */
  string getPropStringValue(string name) {
    result = ((JSONString)getPropValue(name)).getValue()
  }
}

/**
 * An error reported by the JSON parser.
 */
class JSONParseError extends @json_parse_error, Error {
  string getMessage() {
    json_errors(this, result)
  }
}
