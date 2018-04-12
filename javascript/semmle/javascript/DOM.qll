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

/**
 * Provides classes for working with DOM elements.
 */

import javascript
import semmle.javascript.frameworks.Templating

module DOM {
  /**
   * A definition of a DOM element, for instance by an HTML element in an HTML file
   * or a JSX element in a JavaScript file.
   */
  abstract class ElementDefinition extends Locatable {
    /**
     * Gets the name of the DOM element; for example, a `<p>` element has
     * name `p`.
     */
    abstract string getName();

    /**
     * Gets the `i`th attribute of this DOM element, if it can be determined.
     *
     * For example, the 0th (and only) attribute of `<a href="https://semmle.com">Semmle</a>`
     * is `href="https://semmle.com"`.
     */
    AttributeDefinition getAttribute(int i) {
      none()
    }

    /**
     * Gets an attribute of this DOM element with name `name`.
     *
     * For example, the DOM element `<a href="https://semmle.com">Semmle</a>`
     * has a single attribute `href="https://semmle.com"` with the name `href`.
     */
    AttributeDefinition getAttributeByName(string name) {
      result.getElement() = this and
      result.getName() = name
    }

    /**
     * Gets an attribute of this DOM element.
     */
    AttributeDefinition getAnAttribute() {
      result.getElement() = this
    }

    /**
     * Gets the parent element of this element.
     */
    abstract ElementDefinition getParent();

    /**
     * Gets the root element (i.e. an element without a parent) in which this element is contained.
     */
    ElementDefinition getRoot() {
      if not exists(getParent()) then
        result = this
      else
        result = getParent().getRoot()
    }

    /**
     * Gets the document element to which this element belongs, if it can be determined.
     */
    DocumentElementDefinition getDocument() { result = getRoot() }
  }

  /**
   * An HTML element, viewed as an `ElementDefinition`.
   */
  private class HtmlElementDefinition extends ElementDefinition, @xmlelement {
    HtmlElementDefinition() { this instanceof HTMLElement }

    override string getName() { result = this.(HTMLElement).getName() }

    override AttributeDefinition getAttribute(int i) {
      result = this.(HTMLElement).getAttribute(i)
    }

    override ElementDefinition getParent() {
      result = this.(HTMLElement).getParent()
    }
  }

  /**
   * A JSX element, viewed as an `ElementDefinition`.
   */
  private class JsxElementDefinition extends ElementDefinition, @jsxelement {
    JsxElementDefinition() { this instanceof JSXElement }

    override string getName() { result = this.(JSXElement).getName() }

    override AttributeDefinition getAttribute(int i) {
      result = this.(JSXElement).getAttribute(i)
    }

    override ElementDefinition getParent() {
      result = this.(JSXElement).getJsxParent()
    }

  }

  /**
   * A DOM attribute as defined, for instance, by an HTML attribute in an HTML file
   * or a JSX attribute in a JavaScript file.
   */
  abstract class AttributeDefinition extends Locatable {
    /**
     * Gets the name of this attribute, if any.
     *
     * JSX spread attributes do not have a name.
     */
    abstract string getName();

    /**
     * Gets the data flow node whose value is the value of this attribute,
     * if any.
     *
     * This is undefined for HTML elements, where the attribute value is not
     * computed but specified directly.
     */
    DataFlow::Node getValueNode() {
      none()
    }

    /**
     * Gets the value of this attribute, if it can be determined.
     */
    string getStringValue() {
      result = getValueNode().asExpr().getStringValue()
    }

    /**
     * Gets the DOM element this attribute belongs to.
     */
    ElementDefinition getElement() {
      this = result.getAttributeByName(_)
    }

    /**
     * Holds if the value of this attribute might be a template value
     * such as `{{window.location.url}}`.
     */
    predicate mayHaveTemplateValue() {
      getStringValue().regexpMatch(Templating::getDelimiterMatchingRegexp())
    }

  }

  /**
   * An HTML attribute, viewed as an `AttributeDefinition`.
   */
  private class HtmlAttributeDefinition extends AttributeDefinition, @xmlattribute {
    HtmlAttributeDefinition() { this instanceof HTMLAttribute }
    override string getName() { result = this.(HTMLAttribute).getName() }
    override string getStringValue() { result = this.(HTMLAttribute).getValue() }
    override ElementDefinition getElement() { result = this.(HTMLAttribute).getElement() }
  }

  /**
   * A JSX attribute, viewed as an `AttributeDefinition`.
   */
  private class JsxAttributeDefinition extends AttributeDefinition, @jsx_attribute {
    JSXAttribute attr;
    JsxAttributeDefinition() { this = attr }
    override string getName() { result = attr.getName() }
    override DataFlow::Node getValueNode() { result = DataFlow::valueNode(attr.getValue()) }
    override ElementDefinition getElement() { result = attr.getElement() }
  }

  /**
   * An HTML `<document>` element.
   */
  class DocumentElementDefinition extends ElementDefinition {
    DocumentElementDefinition() { this.getName() = "html" }
    override string getName() { none() }
    override AttributeDefinition getAttribute(int i) { none() }
    override AttributeDefinition getAttributeByName(string name) { none() }
    override ElementDefinition getParent() { none() }
  }

  /**
   * Holds if the value of attribute `attr` is interpreted as a URL.
   */
  predicate isUrlValuedAttribute(AttributeDefinition attr) {
    exists (string eltName, string attrName |
      eltName = attr.getElement().getName() and
      attrName = attr.getName() |
      (eltName = "script" or eltName = "iframe" or eltName = "embed" or
       eltName = "video" or eltName = "audio" or eltName = "source" or
       eltName = "track") and
      attrName = "src"
      or
      (eltName = "link" or eltName = "a" or eltName = "base" or
       eltName = "area") and
      attrName = "href"
      or
      eltName = "form" and
      attrName = "action"
      or
      (eltName = "input" or eltName = "button") and
      attrName = "formaction"
    )
  }

  /**
   * A data flow node or other program element that may refer to
   * a DOM element.
   */
  abstract class Element extends Locatable {
    ElementDefinition defn;

    /** Gets the definition of this element. */
    ElementDefinition getDefinition() {
      result = defn
    }

    /** Gets the tag name of this DOM element. */
    string getName() {
      result = defn.getName()
    }

    /** Gets the `i`th attribute of this DOM element, if it can be determined. */
    AttributeDefinition getAttribute(int i) {
      result = defn.getAttribute(i)
    }

    /** Gets an attribute of this DOM element with the given `name`. */
    AttributeDefinition getAttributeByName(string name) {
      result = defn.getAttributeByName(name)
    }
  }

  /**
   * The default implementation of `Element`, including both
   * element definitions and data flow nodes that may refer to them.
   */
  private class DefaultElement extends Element {
    DefaultElement() {
      defn = this
      or
      exists (Element that |
        this.(Expr).flow().getALocalSource().asExpr() = that and
        defn = that.getDefinition()
      )
    }
  }

  /**
   * Holds if `attr` is an invalid id attribute because of `reason`.
   */
  predicate isInvalidHtmlIdAttributeValue(DOM::AttributeDefinition attr, string reason) {
    attr.getName() = "id" and
    exists (string v | v = attr.getStringValue() |
      v = "" and
      reason = "must contain at least one character"
      or
      v.regexpMatch(".*\\s.*") and
      reason = "must not contain any space characters"
    )
  }

}

/**
 * DEPRECATED: Use `DOM::ElementDefinition` instead.
 *
 * A DOM element as defined either by an HTML element in an HTML file
 * or a JSX element in a JavaScript file.
 */
deprecated
class DOMElementDefinition extends Locatable {
  DOMElementDefinition() {
    this instanceof DOM::ElementDefinition
  }

  /**
   * Gets the name of the DOM element; for example, a `<p>` element has
   * name `p`.
   */
  string getName() {
    result = this.(DOM::ElementDefinition).getName()
  }

  /**
   * Gets the `i`th attribute of this DOM element.
   *
   * For example, the 0th (and only) attribute of `<a href="https://semmle.com">Semmle</a>`
   * is `href="https://semmle.com"`.
   */
  DOMAttributeDefinition getAttribute(int i) {
    result = this.(DOM::ElementDefinition).getAttribute(i)
  }

  /**
   * Gets an attribute of this DOM element with name `name`.
   *
   * For example, the DOM element `<a href="https://semmle.com">Semmle</a>`
   * has a single attribute `href="https://semmle.com"` with the name `href`.
   */
  DOMAttributeDefinition getAttributeByName(string name) {
    result = this.(DOM::ElementDefinition).getAttributeByName(name)
  }

  /**
   * Gets the document element to which this element belongs.
   */
  DocumentElement getRoot() {
    result = this.(DOM::ElementDefinition).getRoot()
  }
}

/**
 * DEPRECATED: Use `DOM::AttributeDefinition` instead.
 *
 * A DOM attribute as defined either by an HTML attribute in an HTML file
 * or a JSX attribute in a JavaScript file.
 */
deprecated
class DOMAttributeDefinition extends Locatable {
  DOMAttributeDefinition() {
    this instanceof DOM::AttributeDefinition
  }

  /**
   * Gets the name of this attribute, if any.
   *
   * JSX spread attributes do not have a name.
   */
  string getName() {
    result = this.(DOM::AttributeDefinition).getName()
  }

  /**
   * Gets the value of this attribute, if any.
   *
   * This is undefined for JSX attributes with interpolated values,
   * and spread attributes.
   */
  string getStringValue() {
    result = this.(DOM::AttributeDefinition).getStringValue()
  }

  /**
   * Gets the DOM element this attribute belongs to.
   */
  DOMElementDefinition getElement() {
    result = this.(DOM::AttributeDefinition).getElement()
  }
}

/**
 * DEPRECATED: Use `DOM::DocumentElementDefinition` instead.
 *
 * An HTML document element.
 */
deprecated
class DocumentElement extends DOMElementDefinition {
  DocumentElement() { getName() = "html" }
}

/**
 * DEPRECATED: Use `DOM::isUrlValuedAttribute` instead.
 *
 * A DOM attribute whose value is a URL.
 */
deprecated
class URLValuedAttribute extends DOMAttributeDefinition {
  URLValuedAttribute() {
    DOM::isUrlValuedAttribute(this)
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

/**
 * DEPRECATED: Use `Expr.accessesGlobal` instead.
 *
 * Holds if `e` accesses the global variable `g`, either directly
 * or through the `window` object.
 */
deprecated
predicate accessesGlobal(Expr e, string g) {
  e.accessesGlobal(g)
}
