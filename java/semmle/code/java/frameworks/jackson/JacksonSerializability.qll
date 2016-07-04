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
 * A library for working with Java Serialization in the context of
 * the `com.fasterxml.jackson` JSON processing framework.
 */

import default
import semmle.code.java.Serializability

class JacksonJSONIgnoreAnnotation extends NonReflectiveAnnotation {
	JacksonJSONIgnoreAnnotation() {
		exists (AnnotationType anntp | anntp = this.getType() |
			anntp.hasQualifiedName("com.fasterxml.jackson.annotation", "JsonIgnore") 
		)
	}	
}

abstract class JacksonSerializableType extends Type {
}

/**
 * A method used for serializing objects using Jackson. The final parameter is the object to be
 * serialized.
 */
library class JacksonWriteValueMethod extends Method {
	JacksonWriteValueMethod() {
		(
			getDeclaringType().hasQualifiedName("com.fasterxml.jackson.databind", "ObjectWriter") or
			getDeclaringType().hasQualifiedName("com.fasterxml.jackson.databind", "ObjectMapper")
		) and
		getName().matches("writeValue%") and
		getParameter(getNumberOfParameters() - 1).getType() instanceof TypeObject
	}
}

library class ExplicitlyWrittenJacksonSerializableType extends JacksonSerializableType {
	ExplicitlyWrittenJacksonSerializableType() {
		exists( MethodAccess ma |
			// A call to a Jackson write method...
			ma.getMethod() instanceof JacksonWriteValueMethod and
			// ...where `this` is used in the final argument, indicating that this type will be serialized.
			usesType(ma.getArgument(ma.getNumArgument() - 1).getType(), this)
		)
	}
}

library class FieldReferencedJacksonSerializableType extends JacksonSerializableType {
	FieldReferencedJacksonSerializableType() {
		exists(JacksonSerializableField f | usesType(f.getType(), this))
	}
}

abstract class JacksonDeserializableType extends Type {
}

library class ExplicitlyReadJacksonDeserializableType extends JacksonDeserializableType {
	ExplicitlyReadJacksonDeserializableType() {
		exists( MethodAccess m , TypeLiteral tl |
			usesType(tl.getTypeName().getType(), this) and
			m.getAnArgument() = tl and
			exists (RefType decl | decl = m.getMethod().getDeclaringType() |
				decl.hasQualifiedName("com.fasterxml.jackson.databind", "ObjectReader") or
				decl.hasQualifiedName("com.fasterxml.jackson.databind", "ObjectMapper")
			)
		)
	}
}

library class FieldReferencedJacksonDeSerializableType extends JacksonDeserializableType {
	FieldReferencedJacksonDeSerializableType() {
		exists(JacksonDeserializableField f | usesType(f.getType(), this))
	}
}

class JacksonSerializableField extends SerializableField {
	JacksonSerializableField(){
		exists(JacksonSerializableType superType |
			superType = getDeclaringType().getASupertype*() and
			not superType instanceof TypeObject and
			superType.fromSource()
		) and
		not this.getAnAnnotation() instanceof JacksonJSONIgnoreAnnotation
	}
}

class JacksonDeserializableField extends DeserializableField {
	JacksonDeserializableField(){
		exists(JacksonDeserializableType superType |
			superType = getDeclaringType().getASupertype*() and
			not superType instanceof TypeObject and
			superType.fromSource()
		) and
		not this.getAnAnnotation() instanceof JacksonJSONIgnoreAnnotation
	}
}
