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

/** A `<lookup-method>` element in a Spring XML file. */
class SpringLookupMethod extends SpringXMLElement {
  SpringLookupMethod() {
    this.getName() = "lookup-method"
  }

  /** Gets the value of the `bean` attribute. */
  string getBeanName() {
    result = this.getAttributeValue("bean")
  }

  /** Gets the bean referred to by the `bean` attribute. */
  SpringBean getBean() {
    result.getBeanIdentifier() = this.getBeanName()
  }

  /** Gets the value of the `name` attribute. */
  string getMethodName() {
    result = this.getAttributeValue("name")
  }

  /**
   * The Java method referred to by the lookup-method element.
   *
   * This always looks up the method using the declaring bean of the `<lookup-method>` element.
   * To find the Java method in a child bean, see `getMethod(SpringBean)`.
   */
  Method getMethod() {
    exists (RefType superType |
      this.getEnclosingBean().getClass().hasMethod(result, superType) and
      result.getName() = this.getMethodName()
    )
  }

  /**
   * The Java method referred to by the `lookup-method` element, within a context.
   * This method uses the "class" attribute of the context as the declaring
   * class of the Java method. The parameter context must be the same as or a
   * child bean of the declaring bean of this lookup-method.
   */
  Method getMethod(SpringBean context) {
    this.getEnclosingBean() = context.getBeanParent*() and
    exists (RefType superType |
      context.getClass().hasMethod(result, superType) and
      result.getName() = this.getMethodName()
    )
  }
}
