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
 * Provides classes and predicates for working with the Kryo serialization framework.
 */

import java

/**
 * The type `com.esotericsoftware.kryo.Kryo`.
 */
class Kryo extends RefType {
  Kryo() {
    this.hasQualifiedName("com.esotericsoftware.kryo", "Kryo")
  }
}

/**
 * A Kryo input stream.
 */
class KryoInput extends RefType {
  KryoInput() {
    this.hasQualifiedName("com.esotericsoftware.kryo.io", "Input")
  }
}

/**
 * A Kryo method that deserializes an object.
 */
class KryoReadObjectMethod extends Method {
  KryoReadObjectMethod() {
    this.getDeclaringType() instanceof Kryo and
    (
      this.hasName("readClassAndObject") or
      this.hasName("readObject") or
      this.hasName("readObjectOrNull")
    )
  }
}

/**
 * A call to `Kryo.setRegistrationRequired` that enables white-listing.
 */
class KryoEnableWhiteListing extends MethodAccess {
  KryoEnableWhiteListing() {
    exists(Method m |
      m = this.getMethod() and
      m.getDeclaringType() instanceof Kryo and
      m.hasName("setRegistrationRequired") and
      this.getAnArgument().(BooleanLiteral).getBooleanValue() = true
    )
  }
}
