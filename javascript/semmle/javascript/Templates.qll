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

import Expr

/** A tagged template literal expression. */
class TaggedTemplateExpr extends Expr, @taggedtemplateexpr {
  /** Get the tagging expression of this tagged template. */
  Expr getTag() {
    result = getChildExpr(0)
  }

  /** Get the tagged template itself. */
  TemplateLiteral getTemplate() {
    result = getChildExpr(1)
  }

  predicate isImpure() {
    any()
  }
}

/** A template literal. */
class TemplateLiteral extends Expr, @templateliteral {
  /**
   * Get the i-th element of this template literal, which may either
   * be an interpolated expression or a constant template element.
   */
  Expr getElement(int i) {
    result = getChildExpr(i)
  }

  /**
   * Get an element of this template literal.
   */
  Expr getAnElement() {
    result = getElement(_)
  }

  predicate isImpure() {
    getAnElement().isImpure()
  }
}

/** A constant template element. */
class TemplateElement extends Expr, @templateelement {
  /** Get the value of this template element. */
  string getValue() {
    literals(result, _, this)
  }
  
  /** Get the raw value of this template element. */
  string getRawValue() {
    literals(_, result, this)
  }

  predicate isImpure() {
    none()
  }
}
