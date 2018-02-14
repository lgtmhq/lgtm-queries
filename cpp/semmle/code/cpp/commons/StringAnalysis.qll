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
import semmle.code.cpp.controlflow.SSA

/**
 * Can a value flow directly from one expr to another?
 */
predicate canValueFlow(Expr fromExpr, Expr toExpr)
{
  (
    // value propagated via a definition use pair
    exists(Variable v, SsaDefinition def | fromExpr = def.getAnUltimateDefiningValue(v) |
      toExpr = def.getAUse(v)
    )
  ) or (
    // expr -> containing parenthesized expression
    fromExpr = toExpr.(ParenthesisExpr).getExpr()
  ) or (
    // R value -> containing assignment expression ('=' assignment)
    fromExpr = toExpr.(AssignExpr).getRValue()
  ) or (
    // then -> containing ternary (? :) operator
    fromExpr = toExpr.(ConditionalExpr).getThen()
  ) or (
    // else -> containing ternary (? :) operator
    fromExpr = toExpr.(ConditionalExpr).getElse()
  )
}

/**
 * An analysed null terminated string.  Returns maximum string length (including null) when
 * it can be calculated.
 */
class AnalysedString extends Expr
{
  AnalysedString()
  {
    this.getType().getUnspecifiedType() instanceof ArrayType or
    this.getType().getUnspecifiedType() instanceof PointerType
  }

  int getMaxLength()
  {
    // otherwise, take the longest AnalysedString it's value could 'flow' from; however if even one doesn't
    // return a value (this essentially means 'infinity') we can't return a value either.
    result = max(AnalysedString expr, int toMax | (canValueFlow*(expr, this)) and (toMax = expr.(StringLiteral).getOriginalLength()) | toMax) // maximum length
    and
    forall(AnalysedString expr | canValueFlow(expr, this) | exists(expr.getMaxLength())) // all sources return a value (recursive)
  }
}

/**
 * A call to a strlen like function.
 */
class StrlenCall extends FunctionCall {
  StrlenCall() {
    this.getTarget().hasQualifiedName("strlen") or
    this.getTarget().hasQualifiedName("wcslen") or
    this.getTarget().hasQualifiedName("_mbslen") or
    this.getTarget().hasQualifiedName("_mbslen_l") or
    this.getTarget().hasQualifiedName("_mbstrlen") or
    this.getTarget().hasQualifiedName("_mbstrlen_l")
  }

  /**
   * The string argument passed into this strlen-like call.
   */
  Expr getStringExpr() {
    result = this.getArgument(0)
  }
}
