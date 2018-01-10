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

import semmle.code.cpp.exprs.Expr

/**
 * A C/C++ comparison operation, that is, either an equality operation or a relational operation.
 */
abstract class ComparisonOperation extends BinaryOperation {
}

/**
 * A C/C++ equality operation, that is, either "==" or "!=".
 */
abstract class EqualityOperation extends ComparisonOperation {
  override int getPrecedence() { result = 9 }
}

/**
 * A C/C++ equal expression.
 */
class EQExpr extends EqualityOperation, @eqexpr {
  override string getOperator() { result = "==" }
}

/**
 * A C/C++ not equal expression.
 */
class NEExpr extends EqualityOperation, @neexpr {
  override string getOperator() { result = "!=" }
}

/**
 * A C/C++ relational operation, that is, one of `<=`, `<`, `>`, or `>=`.
 */
abstract class RelationalOperation extends ComparisonOperation {
  override int getPrecedence() { result = 10 }

  /**
   * DEPRECATED: Use `getGreaterOperand()` instead.
   */
  deprecated
  Expr getLarge() {
    result = getGreaterOperand()
  }

  /**
   * DEPRECATED: Use `getLesserOperand()` instead.
   */
  deprecated
  Expr getSmall() {
    result = getLesserOperand()
  }

  /**
   * Gets the operand on the "greater" (or "greater-or-equal") side
   * of this relational expression, that is, the side that is larger
   * if the overall expression evaluates to `true`; for example on
   * `x <= 20` this is the `20`, and on `y > 0` it is `y`.
   */
  abstract Expr getGreaterOperand();

  /**
   * Gets the operand on the "lesser" (or "lesser-or-equal") side
   * of this relational expression, that is, the side that is smaller
   * if the overall expression evaluates to `true`; for example on
   * `x <= 20` this is `x`, and on `y > 0` it is the `0`.
   */
  abstract Expr getLesserOperand();
}

/**
 * A C/C++ greater than expression.
 */
class GTExpr extends RelationalOperation, @gtexpr {
  override string getOperator() { result = ">" }
 
  override Expr getGreaterOperand() { result = getLeftOperand() }
  override Expr getLesserOperand() { result = getRightOperand() }
}

/**
 * A C/C++ lesser than expression.
 */
class LTExpr extends RelationalOperation, @ltexpr {
  override string getOperator() { result = "<" }

  override Expr getGreaterOperand() { result = getRightOperand() }
  override Expr getLesserOperand() { result = getLeftOperand() }
}

/**
 * A C/C++ greater than or equal expression.
 */
class GEExpr extends RelationalOperation, @geexpr {
  override string getOperator() { result = ">=" }

  override Expr getGreaterOperand() { result = getLeftOperand() }
  override Expr getLesserOperand() { result = getRightOperand() }
}

/**
 * A C/C++ lesser than or equal expression.
 */
class LEExpr extends RelationalOperation, @leexpr {
  override string getOperator() { result = "<=" }

  override Expr getGreaterOperand() { result = getRightOperand() }
  override Expr getLesserOperand() { result = getLeftOperand() }
}
