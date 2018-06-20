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

/** A common supertype of `SpringRef` and `SpringIdRef`. */
class SpringAbstractRef extends SpringXMLElement {
  SpringAbstractRef() {
    this.getName() = "idref" or
    this.getName() = "ref"
  }

  /** Holds if this reference has a bean attribute. */
  predicate hasBeanName() {
    this.hasAttribute("bean")
  }

  /** The value of the bean attribute. */
  string getBeanName() {
    result = this.getAttributeValue("bean")
  }

  /** Holds if this reference has a local attribute. */
  predicate hasBeanLocalName() {
    this.hasAttribute("local")
  }

  /** The value of the local attribute. */
  string getBeanLocalName() {
    result = this.getAttributeValue("local")
  }

  /** The bean pointed to by this reference. */
  SpringBean getBean() {
    if this.hasBeanLocalName()
    then result.getBeanId() = this.getBeanLocalName()
    else result.getBeanIdentifier() = this.getBeanName()
  }

  /** Holds if `other` is also a reference and points to the same bean as this reference. */
  override predicate isSimilar(SpringXMLElement other) {
    exists (SpringAbstractRef otherRef |
      otherRef = other and
      this.getBean() = otherRef.getBean()
    )
  }
}
