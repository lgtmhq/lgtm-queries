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
import semmle.code.java.frameworks.spring.SpringBeanFile
import semmle.code.java.frameworks.spring.SpringBean

/** A common superclass for all Spring XML elements. */
class SpringXMLElement extends XMLElement {
  SpringXMLElement() {
    this.getFile() instanceof SpringBeanFile
  }

  /** Gets a child of this Spring XML element. */
  SpringXMLElement getASpringChild() {
    result = this.getAChild()
  }

  /** Gets the bean file of this XML element. */
  SpringBeanFile getSpringBeanFile() {
    result = this.getFile()
  }

  /**
   * Gets the value of the attribute with name `attributeName`, or "default" if the
   * attribute is not present.
   */
  string getAttributeValueWithDefault(string attributeName) {
    this.hasAttribute(attributeName) and
    if exists(XMLAttribute a | a = this.getAttribute(attributeName))
      then result = this.getAttributeValue(attributeName)
      else result = "default"
  }

  /** Gets the closest enclosing `<bean>` element. */
  SpringBean getEnclosingBean() {
    if this instanceof SpringBean
    then result = this
    else result = this.getParent().(SpringXMLElement).getEnclosingBean()
  }

  /**
   * Overridden by subclasses. Used to match `value`, `property` and `ref` elements for similarity.
   */
  predicate isSimilar(SpringXMLElement other) {
    none()
  }

  string getContentString() {
    result = this.allCharactersString()
  }
}
