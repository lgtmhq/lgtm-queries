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
 * A library for working with Java Serialization.
 */

import default
private import frameworks.jackson.JacksonSerializability

/**
 * A serializable field may be read without code referencing it,
 * due to the use of serialization.
 */
abstract class SerializableField extends Field {
	
}
/**
 * A deserializable field may be written without code referencing it,
 * due to the use of serialization.
 */
abstract class DeserializableField extends Field {
	
}

/**
 * A non-`transient` field in a type that (directly or indirectly) implements the `Serializable` interface
 * and may be read or written via serialization.
 */
library class StandardSerializableField extends SerializableField, DeserializableField {
	StandardSerializableField(){
		this.getDeclaringType().getASupertype*().hasName("Serializable") and
		not this.isTransient()
	}
}
