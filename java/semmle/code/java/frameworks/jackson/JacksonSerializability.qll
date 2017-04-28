// Copyright 2017 Semmle Ltd.
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
 * Provides classes and predicates for working with Java Serialization in the context of
 * the `com.fasterxml.jackson` JSON processing framework.
 */

import java
import semmle.code.java.Serializability
import semmle.code.java.Reflection

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

/**
 * A call to the `addMixInAnnotations` or `addMixIn` Jackson method.
 *
 * This informs Jackson to treat the annotations on the second class argument as if they were on
 * the first class argument. This allows adding annotations to library classes, for example.
 */
class JacksonAddMixinCall extends MethodAccess {
  JacksonAddMixinCall() {
    exists(Method m |
      m = this.getMethod() and
      m.getDeclaringType().hasQualifiedName("com.fasterxml.jackson.databind", "ObjectMapper") |
      m.hasName("addMixIn") or
      m.hasName("addMixInAnnotations")
    )
  }

  /**
   * Get a possible type for the target of the mixing, if any can be deduced.
   */
  RefType getATarget() {
    result = inferClassParameterType(getArgument(0))
  }

  /**
   * Get a possible type that will be mixed in, if any can be deduced.
   */
  RefType getAMixedInType() {
    result = inferClassParameterType(getArgument(1))
  }
}

/**
 * A Jackson annotation.
 */
class JacksonAnnotation extends Annotation {
  JacksonAnnotation() {
    getType().getPackage().hasName("com.fasterxml.jackson.annotation")
  }
}

/**
 * A type used as a Jackson mixin type.
 */
class JacksonMixinType extends ClassOrInterface {
  JacksonMixinType() {
    exists(JacksonAddMixinCall mixinCall |
      this = mixinCall.getAMixedInType()
    )
  }

  /**
   * Get a type that this type is mixed into.
   */
  RefType getATargetType() {
    exists(JacksonAddMixinCall mixinCall |
      this = mixinCall.getAMixedInType() |
      result = mixinCall.getATarget())
  }

  /**
   * Get a callable from this type which is mixed in by Jackson.
   */
  Callable getAMixedInCallable() {
    result = getACallable() and
    (
      result.(Constructor).isDefaultConstructor() or
      result.getAnAnnotation() instanceof JacksonAnnotation or
      result.getAParameter().getAnAnnotation() instanceof JacksonAnnotation
    )
  }

  /**
   * Get a field that is mixed in by Jackson.
   */
  Field getAMixedInField() {
    result = getAField() and
    result.getAnAnnotation() instanceof JacksonAnnotation
  }
}

class JacksonMixedInCallable extends Callable {
  JacksonMixedInCallable() {
    exists(JacksonMixinType mixinType |
      this = mixinType.getAMixedInCallable()
    )
  }

  /**
   * Get a candidate target type that this callable can be mixed into.
   */
  RefType getATargetType() {
    exists(JacksonMixinType mixinType |
      this = mixinType.getAMixedInCallable() |
      result = mixinType.getATargetType()
    )
  }

  /**
   * Get a callable on a possible target that this is mixed into.
   */
  Callable getATargetCallable() {
    exists(RefType targetType |
      targetType = getATargetType() |
      result = getATargetType().getACallable() and
      if this instanceof Constructor then
        /*
         * The mixed in type will have a different name to the target type, so just compare the
         * parameters.
         */
        result.getSignature().suffix(targetType.getName().length()) = getSignature().suffix(getDeclaringType().getName().length())
      else
        // Signatures should match
        result.getSignature() = getSignature()
    )
  }
}