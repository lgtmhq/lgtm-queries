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
import semmle.code.java.frameworks.spring.SpringXMLElement

/** A `<qualifier>` element in a Spring XML file. */
class SpringQualifier extends SpringXMLElement {
  SpringQualifier() {
    this.getName() = "qualifier"
  }

  /** Gets the name of the Java class of this qualifier. */
  string getQualifierTypeName() {
    if this.hasAttribute("type")
    then result = this.getAttributeValue("type")
    else result = "org.springframework.beans.factory.annotation.Qualifier"
  }

  /** Holds if this qualifier has a `value` attribute. */
  predicate hasQualifierValue() {
    this.hasAttribute("value")
  }

  /** Gets the value of the `value` attribute. */
  string getQualifierValue() {
    result = this.getAttributeValue("value")
  }
}
