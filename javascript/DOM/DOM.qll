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

/**
 * Provides classes for working with DOM elements.
 */

import javascript

/**
 * A DOM element as defined either by an HTML element in an HTML file
 * or a JSX element in a JavaScript file.
 */
class DOMElementDefinition extends Locatable {
  DOMElementDefinition() {
    this instanceof HTMLElement or
    this instanceof JSXElement
  }

  /**
   * Gets the name of the DOM element; for example, a `<p>` element has
   * name `p`.
   */
  string getName() {
    result = this.(HTMLElement).getName() or
    result = this.(JSXElement).getName()
  }

  /**
   * Gets the `i`th attribute of this DOM element.
   *
   * For example, the 0th (and only) attribute of `<a href="https://semmle.com">Semmle</a>`
   * is `href="https://semmle.com"`.
   */
  DOMAttributeDefinition getAttribute(int i) {
    result = this.(HTMLElement).getAttribute(i) or
    result = this.(JSXElement).getAttribute(i)
  }

  /**
   * Gets an attribute of this DOM element with name `name`.
   *
   * For example, the DOM element `<a href="https://semmle.com">Semmle</a>`
   * has a single attribute `href="https://semmle.com"` with the name `href`.
   */
  DOMAttributeDefinition getAttributeByName(string name) {
    result = this.(HTMLElement).getAttributeByName(name) or
    result = this.(JSXElement).getAttributeByName(name)
  }

  /**
   * Gets the document element to which this element belongs.
   */
  DocumentElement getRoot() {
    result = this.(HTMLElement).getParent*()
  }
}

/**
 * A DOM attribute as defined either by an HTML attribute in an HTML file
 * or a JSX attribute in a JavaScript file.
 */
class DOMAttributeDefinition extends Locatable {
  DOMAttributeDefinition() {
    this instanceof HTMLAttribute or
    this instanceof JSXAttribute
  }

  /**
   * Gets the name of this attribute, if any.
   *
   * JSX spread attributes do not have a name.
   */
  string getName() {
    result = this.(HTMLAttribute).getName() or
    result = this.(JSXAttribute).getName()
  }

  /**
   * Gets the value of this attribute, if any.
   *
   * This is undefined for JSX attributes with interpolated values,
   * and spread attributes.
   */
  string getStringValue() {
    result = this.(HTMLAttribute).getValue() or
    result = this.(JSXAttribute).getStringValue()
  }

  /**
   * Gets the DOM element this attribute belongs to.
   */
  DOMElementDefinition getElement() {
    this = result.getAttribute(_)
  }
}

/**
 * An HTML document element.
 */
class DocumentElement extends DOMElementDefinition {
  DocumentElement() { getName() = "html" }
}

/**
 * Holds if the value of attribute `attrName` of element `eltName` looks like
 * a URL.
 */
private predicate urlValued(string eltName, string attrName) {
  (eltName = "script" or eltName = "iframe" or eltName = "embed" or
   eltName = "video" or eltName = "audio" or eltName = "source" or
   eltName = "track") and
   attrName = "src" or

  (eltName = "link" or eltName = "a" or eltName = "base" or
   eltName = "area") and
   attrName = "href" or

  eltName = "form" and
   attrName = "action" or

  (eltName = "input" or eltName = "button") and
   attrName = "formaction"
}

/**
 * A DOM attribute whose value is a URL.
 */
class URLValuedAttribute extends DOMAttributeDefinition {
  URLValuedAttribute() {
    urlValued(getElement().getName(), getName())
  }

  /**
   * Gets the URL value of this attribute.
   *
   * No attempt is made to resolve relative URLs; they are returned as-is.
   */
  string getURL() {
    result = getStringValue().trim()
  }
}