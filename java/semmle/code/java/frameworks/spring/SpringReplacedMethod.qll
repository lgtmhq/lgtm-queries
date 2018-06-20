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
import semmle.code.java.frameworks.spring.SpringBean

/** A `<replaced-method>` element in a Spring XML file. */
class SpringReplacedMethod extends SpringXMLElement {
  SpringReplacedMethod() {
    this.getName() = "replaced-method"
  }

  /** The value of the `name` attribute. */
  string getMethodName() {
    result = this.getAttributeValue("name")
  }

  /** The value of the `replacer` attribute. */
  string getReplacerBeanName() {
    result = this.getAttributeValue("replacer")
  }

  /** The bean referred to by the `replacer` attribute. */
  SpringBean getReplacerBean() {
    result.getBeanIdentifier() = this.getReplacerBeanName()
  }
}
