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
import semmle.code.java.frameworks.spring.SpringAbstractRef

/** A `<ref>` element in a Spring XML file. */
class SpringRef extends SpringAbstractRef {
  SpringRef() {
    this.getName() = "ref"
  }

  /** Holds if this `ref` has a `parent` attribute. */
  predicate hasBeanNameInParent() {
    this.hasAttribute("parent")
  }

  /** The value of the `parent` attribute. */
  string getBeanNameInParent() {
    result = this.getAttributeValue("parent")
  }

  /** The bean referred to by the `ref` element. */
  override SpringBean getBean() {
    if this.hasBeanLocalName()
    then result.getBeanId() = this.getBeanLocalName()
    else result.getBeanIdentifier() = this.getBeanName()
  }
}
