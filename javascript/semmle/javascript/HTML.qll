// Copyright 2017 Semmle Ltd.
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

import Locations

/**
 * An HTML file, that is, a file with extension
 * `html`, `htm`, `xhtml` or `xhtm` (regardless of case).
 */
class HTMLFile extends File {
  HTMLFile() {
    getExtension().regexpMatch("(?i)x?html?")
  }
}

/**
 * An HTML element like `<a href="semmle.com">Semmle</a>`.
 */
class HTMLElement extends Locatable, @xmlelement {
  HTMLElement() {
    exists (HTMLFile f | xmlElements(this, _, _, _, f))
  }

  Location getLocation() {
    xmllocations(this, result)
  }

  string getName() {
    xmlElements(this, result, _, _, _)
  }

  /**
   * Get the parent element of this element, if any.
   */
  HTMLElement getParent() {
    xmlElements(this, _, result, _, _)
  }

  /**
   * Is this a top-level element without a parent element?
   */
  predicate isTopLevel() {
    not exists(getParent())
  }

  /**
   * Get the `i`-th child element (0-based) of this element.
   */
  HTMLElement getChild(int i) {
    xmlElements(result, _, this, i, _)
  }

  /**
   * Get a child element of this element.
   */
  HTMLElement getChild() {
    result = getChild(_)
  }

  /**
   * Get the `i`-th attribute (0-based) of this element.
   */
  HTMLAttribute getAttribute(int i) {
    xmlAttrs(result, this, _, _, i, _)
  }

  /**
   * Get an attribute of this element.
   */
  HTMLAttribute getAnAttribute() {
    result = getAttribute(_)
  }

  /**
   * Get an attribute of this element that has the given name.
   */
  HTMLAttribute getAttributeByName(string name) {
    result = getAnAttribute() and
    result.getName() = name
  }

  string toString() {
    result = "<" + getName() + ">...</>"
  }
}

/**
 * An attribute of an HTML element.
 *
 * For example, the element `<a href ="semmle.com" target=_blank>Semmle</a>`
 * has two attributes: `href ="semmle.com"` and `target=_blank`.
 */
class HTMLAttribute extends Locatable, @xmlattribute {
  HTMLAttribute() {
    exists (HTMLFile f | xmlAttrs(this, _, _, _, _, f))
  }

  Location getLocation() {
    xmllocations(this, result)
  }

  /**
   * Get the element to which this attribute belongs.
   */
  HTMLElement getElement() {
    xmlAttrs(this, result, _, _, _, _)
  }

  /**
   * Get the name of this attribute.
   */
  string getName() {
    xmlAttrs(this, _, result, _, _, _)
  }

  /**
   * Get the value of this attribute.
   *
   * For attributes without an explicitly specified value, the
   * result is the empty string.
   */
  string getValue() {
    xmlAttrs(this, _, _, result, _ ,_)
  }

  string toString() {
    result = getName() + "=" + getValue()
  }
}