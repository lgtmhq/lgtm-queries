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
 * Library for working with DOM elements.
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
   * The name of the DOM element; for example, a `<p>` element has
   * name `p`.
   */
  string getName() {
    result = this.(HTMLElement).getName() or
    result = this.(JSXElement).getName()
  }

  /**
   * The `i`-th attribute of this DOM element; for example, the
   * 0-th (and only) attribute of `<a href="https://semmle.com">Semmle</a>`
   * is `href="https://semmle.com"`.
   */
  DOMAttributeDefinition getAttribute(int i) {
    result = this.(HTMLElement).getAttribute(i) or
    result = this.(JSXElement).getAttribute(i)
  }

  /**
   * An attribute of this DOM element with the given name; for example,
   * the DOM element `<a href="https://semmle.com">Semmle</a>` has a single
   * attribute `href="https://semmle.com"` with the name `href`.
   */
  DOMAttributeDefinition getAttributeByName(string name) {
    result = this.(HTMLElement).getAttributeByName(name) or
    result = this.(JSXElement).getAttributeByName(name)
  }

  /**
   * The document element to which this element belongs.
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
   * The name of this attribute; not defined for JSX spread attributes.
   */
  string getName() {
    result = this.(HTMLAttribute).getName() or
    result = this.(JSXAttribute).getName()
  }

  /**
   * The value of this attribute; not defined for JSX attributes with
   * interpolated values or spread attributes.
   */
  string getStringValue() {
    result = this.(HTMLAttribute).getValue() or
    result = this.(JSXAttribute).getStringValue()
  }

  /**
   * The DOM element this attribute belongs to.
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
 * The value of attribute `attrName` of element `eltName` may be
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
   * Get the URL value of this attribute; no attempt is made to
   * resolve relative URLs, they are returned as-is.
   */
  string getURL() {
    result = getStringValue().trim()
  }
}