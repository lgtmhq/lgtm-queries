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

/** Provides classes for working with ECMAScript 2015-style template expressions. */

import Expr

/** A tagged template literal expression. */
class TaggedTemplateExpr extends Expr, @taggedtemplateexpr {
  /** Gets the tagging expression of this tagged template. */
  Expr getTag() {
    result = getChildExpr(0)
  }

  /** Gets the tagged template itself. */
  TemplateLiteral getTemplate() {
    result = getChildExpr(1)
  }

  override predicate isImpure() { any() }
}

/** A template literal. */
class TemplateLiteral extends Expr, @templateliteral {
  /**
   * Gets the `i`th element of this template literal, which may either
   * be an interpolated expression or a constant template element.
   */
  Expr getElement(int i) {
    result = getChildExpr(i)
  }

  /**
   * Gets an element of this template literal.
   */
  Expr getAnElement() {
    result = getElement(_)
  }

  override predicate isImpure() { getAnElement().isImpure() }
}

/** A constant template element. */
class TemplateElement extends Expr, @templateelement {
  /** Gets the value of this template element. */
  string getValue() {
    literals(result, _, this)
  }

  /** Gets the raw value of this template element. */
  string getRawValue() {
    literals(_, result, this)
  }

  override predicate isImpure() { none() }
}
