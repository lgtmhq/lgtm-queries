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
 * A library for working with JSX code.
 */

import javascript

/**
 * A JSX element such as `<a href={linkTarget()}>{linkText()}</a>`.
 */
class JSXElement extends Expr, @jsxelement {
  /** Get the expression denoting the name of this element. */
  JSXName getNameExpr() {
    result = getChildExpr(-1)
  }

  /** Get the name of this element. */
  string getName() {
    result = getNameExpr().getValue()
  }

  /** Get the `i`-th attribute of this element. */
  JSXAttribute getAttribute(int i) {
    properties(result, this, i, _, _)
  }

  /** Get some attribute of this element. */
  JSXAttribute getAnAttribute() {
    result = getAttribute(_)
  }

  /** Get an attribute of this element with the given name. */
  JSXAttribute getAttributeByName(string name) {
    result = getAnAttribute() and result.getName() = name
  }

  /** Get the `i`-th element in the body of this element. */
  Expr getBodyElement(int i) {
    i >= 0 and result = getChildExpr(-i-2)
  }
  
  /** Get an element in the body of this element. */
  Expr getABodyElement() {
    result = getBodyElement(_)
  }

  CFGNode getFirstCFGNode() {
    result = getNameExpr().getFirstCFGNode()
  }
}

/**
 * An attribute of a JSX element such as `href={linkTarget()}` or `{...attrs}`.
 */
class JSXAttribute extends ASTNode, @jsx_attribute {
  /**
   * Get the expression denoting the name of this attribute.
   *
   * This is not defined for spread attributes.
   */
  JSXName getNameExpr() {
    result = getChildExpr(0)
  }

  /**
   * Get the name of this attribute.
   *
   * This is not defined for spread attributes.
   */
  string getName() {
    result = getNameExpr().getValue()
  }

  /** Get the expression denoting the value of this attribute. */
  Expr getValue() {
    result = getChildExpr(1)
  }

  /** Get the value of this attribute as a constant string, if possible. */
  string getStringValue() {
    result = getValue().getStringValue()
  }

  /** Get the JSX element to which this attribute belongs. */
  JSXElement getElement() {
    this = result.getAnAttribute()
  }

  CFGNode getFirstCFGNode() {
    result = getNameExpr().getFirstCFGNode() or
    not exists(getNameExpr()) and result = getValue().getFirstCFGNode()
  }

  string toString() {
    properties(this, _, _, _, result)
  }
}

/**
 * A spread attribute of a JSX element, such as `{...attrs}`.
 */
class JSXSpreadAttribute extends JSXAttribute {
  JSXSpreadAttribute() { not exists(getNameExpr()) }

  SpreadElement getValue() {
    // override for more precise result type
    result = super.getValue()
  }
}

/**
 * A namespace-qualified name such as `n:a`.
 */
class JSXQualifiedName extends Expr, @jsxqualifiedname {
  /** Get the namespace component of this qualified name. */
  Identifier getNamespace() {
    result = getChildExpr(0)
  }

  /** Get the name component of this qualified name. */
  Identifier getName() {
    result = getChildExpr(1)
  }

  CFGNode getFirstCFGNode() {
    result = getNamespace().getFirstCFGNode()
  }
}

/**
 * A name of an JSX element or attribute (which is
 * always an identifier, a dot expression, or a qualified
 * namespace name).
 */
class JSXName extends Expr {
  JSXName() {
    this instanceof Identifier or
    this.(DotExpr).getBase() instanceof JSXName or
    this instanceof JSXQualifiedName
  }

  /**
   * The string value of this name.
   */
  string getValue() {
    result = this.(Identifier).getName() or
    exists (DotExpr dot | dot = this |
      result = dot.getBase().(JSXName).getValue() + "." + dot.getPropertyName()
    ) or
    exists (JSXQualifiedName qual | qual = this |
      result = qual.getNamespace() + ":" + qual.getName()
    )
  }
}

/**
 * An interpolating expression that interpolates nothing.
 */
class JSXEmptyExpr extends Expr, @jsxemptyexpr {
}

/**
 * A JSX attribute, viewed as a data flow node that writes properties to 
 * the JSX element it is in.
 */
library class JSXAttributeAsWrite extends PropWriteNode {
  JSXAttributeAsWrite() { exists (JSXAttribute attr | this = attr.getNameExpr()) }
  private JSXAttribute getAttribute() { result.getNameExpr() = this }
  DataFlowNode getBase() { result = getAttribute().getElement() }
  string getPropertyName() { result = this.(JSXName).getValue() }
  DataFlowNode getRhs() { result = getAttribute().getValue() }
}
