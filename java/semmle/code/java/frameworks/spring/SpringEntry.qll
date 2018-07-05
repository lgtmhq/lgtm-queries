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
import semmle.code.java.frameworks.spring.SpringAbstractRef
import semmle.code.java.frameworks.spring.SpringKey
import semmle.code.java.frameworks.spring.SpringValue

/** An `<entry>` element in Spring XML files. */
class SpringEntry extends SpringXMLElement {
  SpringEntry() {
    this.getName() = "entry"
  }

  /** Holds if this `entry` has a `key` attribute. */
  predicate hasKeyString() {
    this.hasAttribute("key")
  }

  /** Gets the value of the `key` attribute. */
  string getKeyString() {
    result = this.getAttributeValue("key")
  }

  /** Holds if this `entry` has a `key-ref` attribute. */
  predicate hasKeyRefString() {
    this.hasAttribute("key-ref")
  }

  /** Gets the value of `key-ref` attribute. */
  string getKeyRefString() {
    result = this.getAttributeValue("key-ref")
  }

  /**
   * The bean pointed to by the `key-ref` attribute, or a nested
   * `<ref>` or `<idref>` element.
   */
  SpringBean getKeyRefBean() {
    if this.hasKeyRefString()
    then result.getBeanIdentifier() = this.getKeyRefString()
    else exists(SpringKey key, SpringAbstractRef ref |
      key = this.getASpringChild() and
      ref = key.getASpringChild() and
      result = ref.getBean()
    )
  }

  /** Holds if this `entry` has a `value` attribute. */
  predicate hasValueStringRaw() {
    this.hasAttribute("value")
  }

  /** Gets the value of the `value` attribute. */
  string getValueStringRaw() {
    result = this.getAttributeValue("value")
  }

  /**
   * The value of the `value` attribute, or a nested `<value>` element, whichever
   * is present.
   */
  string getValueString() {
    if this.hasValueStringRaw()
    then result = this.getValueStringRaw()
    else exists (SpringValue val |
      val = this.getASpringChild() and
      result = val.getContentString()
    )
  }

  /** Holds if this `entry` has a `value-ref` attribute. */
  predicate hasValueRefString() {
    this.hasAttribute("value-ref")
  }

  /** Gets the value of the `value-ref` attribute. */
  string getValueRefString() {
    result = this.getAttributeValue("value-ref")
  }

  /**
   * The bean pointed to by either the `value-ref` attribute, or a nested
   * `<ref> or `<idref>` element, whichever is present.
   */
  SpringBean getValueRefBean() {
    if this.hasValueRefString()
    then result.getBeanIdentifier() = this.getValueRefString()
    else exists(SpringAbstractRef ref |
      ref = this.getASpringChild() and
      result = ref.getBean()
    )
  }
}
