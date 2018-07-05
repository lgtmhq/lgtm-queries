// Copyright 2018 Semmle Ltd.
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

import java
import semmle.code.java.frameworks.spring.SpringMergable

/** A `<map>` element in Spring XML files. */
class SpringMap extends SpringMergable {
  SpringMap() {
    this.getName() = "map"
  }

  /** Gets the value of the `key-type` attribute. */
  string getKeyTypeName() {
    result = this.getAttributeValue("key-type")
  }

  /** Gets the Java `RefType` (class or interface) that is referred to by the `key-type` attribute. */
  RefType getKeyType() {
    result.getQualifiedName() = this.getKeyTypeName()
  }

  /** Gets the value of the `value-type` attribute. */
  string getValueTypeName() {
    result = this.getAttributeValue("value-type")
  }

  /** Gets the Java `RefType` (class or interface) that is referred to by the `value-type` attribute. */
  RefType getValueType() {
    result.getQualifiedName() = this.getValueTypeName()
  }
}
