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

/** An `<alias>` element in Spring XML files. */
class SpringAlias extends SpringXMLElement {
  SpringAlias() {
    this.getName() = "alias"
  }

  /** Gets the value of the `alias` attribute. */
  string getBeanAlias() {
    result = this.getAttributeValue("alias")
  }

  /** Gets the value of the `name` attribute. */
  string getBeanName() {
    result = this.getAttributeValue("name")
  }

  /** Gets the bean referred to by the alias. */
  SpringBean getBean() {
    exists(SpringBean b |
      b.getBeanIdentifier() = this.getBeanName() and
      result = b
    )
  }
}
