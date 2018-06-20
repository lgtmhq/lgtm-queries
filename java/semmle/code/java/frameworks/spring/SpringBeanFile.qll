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
import semmle.code.java.frameworks.spring.SpringBean

/**
 * A Spring XML file.
 *
 * This class includes methods to access attributes of the `<beans>` element.
 */
class SpringBeanFile extends XMLFile {
  SpringBeanFile() {
    count(XMLElement e | e = this.getAChild()) = 1 and
    this.getAChild().getName() = "beans"
  }

  /**
   * A `<bean>` element that is found in this file.
   *
   * Note that this will also include `<bean>` elements nested
   * inside other spring elements (such as `value`).
   *
   * Use `SpringBean.isTopLevel()` to obtain only the `<bean>`
   * elements that are direct children of `<beans>`.
   */
  SpringBean getABean() {
    exists(SpringBean b | b.getFile() = this and result = b)
  }

  /** The `<beans>` element of the file. */
  XMLElement getBeansElement() {
    result = this.getAChild() and
    result.getName() = "beans"
  }

  /**
   * A `profile` expression for which this beans file is enabled, or nothing if it is
   * applicable to any profile.
   */
  string getAProfileExpr() {
    result = getBeansElement().getAttribute("profile").getValue().splitAt(",").splitAt(" ").splitAt(";") and
    result.length() != 0
  }

  /** The `default-autowire` value for this file. */
  string getDefaultAutowire() {
    if this.getBeansElement().hasAttribute("default-autowire")
    then result = this.getBeansElement().getAttributeValue("default-autowire")
    else result = "no"
  }

  /** The `default-autowire-candidates` value for this file. */
  string getDefaultAutowireCandidatesPattern() {
    result = this.getBeansElement().getAttributeValue("default-autowire-candidates")
  }

  /** The `default-dependency-check` value for this file. */
  string getDefaultDependencyCheck() {
    if exists(XMLAttribute a | this.getBeansElement().getAttribute("default-dependency-check") = a)
    then result = this.getBeansElement().getAttributeValue("default-dependency-check")
    else result = "none"
  }

  /** The `default-destroy-method` value for this file. */
  string getDefaultDestroyMethod() {
    result = this.getBeansElement().getAttributeValue("default-destroy-method")
  }

  /** Holds if this file has a `default-destroy-method` value. */
  predicate hasDefaultDestroyMethod() {
    exists(XMLAttribute a | this.getBeansElement().getAttribute("default-destroy-method") = a)
  }

  /** The `default-init-method` value for this file. */
  string getDefaultInitMethod() {
    result = this.getBeansElement().getAttributeValue("default-init-method")
  }

  /** Holds if the file has a `default-destroy-method` value. */
  predicate hasDefaultInitMethod() {
    exists(XMLAttribute a | this.getBeansElement().getAttribute("default-init-method") = a)
  }

  /** Holds if `default-lazy-init` is specified to be `true` for this file. */
  predicate isDefaultLazyInit() {
    exists(XMLAttribute a |
      this.getBeansElement().getAttribute("default-lazy-init") = a and
      a.getValue() = "true"
    )
  }

  /** Holds if `default-merge` is specified to be `true` for this file. */
  predicate isDefaultMerge() {
    exists(XMLAttribute a |
      this.getBeansElement().getAttribute("default-merge") = a and
      a.getValue() = "true"
    )
  }
}
