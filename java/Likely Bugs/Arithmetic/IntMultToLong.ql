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
 * @name Result of multiplication cast to wider type
 * @description Casting the result of a multiplication to a wider type instead of casting
 *              before the multiplication may cause overflow.
 * @kind problem
 * @problem.severity warning
 * @precision very-high
 * @id java/integer-multiplication-cast-to-long
 * @tags reliability
 *       security
 *       correctness
 *       types
 *       external/cwe/cwe-190
 *       external/cwe/cwe-192
 *       external/cwe/cwe-197
 *       external/cwe/cwe-681
 */
import java
import semmle.code.java.dataflow.RangeUtils
import semmle.code.java.Conversions

/** An multiplication that does not overflow. */
predicate small(MulExpr e) {
  exists(NumType t, float lhs, float rhs, float res | t = e.getType() |
    lhs = e.getLeftOperand().getProperExpr().(ConstantIntegerExpr).getIntValue() and
    rhs = e.getRightOperand().getProperExpr().(ConstantIntegerExpr).getIntValue() and
    lhs * rhs = res and
    t.getOrdPrimitiveType().getMinValue() <= res and res <= t.getOrdPrimitiveType().getMaxValue()
  )
}

/**
 * A parent of e, but only one that roughly preserves the value - in particular, not calls.
 */
Expr getRestrictedParent(Expr e) {
  result = e.getParent() and
  (result instanceof ArithExpr or result instanceof ConditionalExpr or result instanceof ParExpr)
}

from ConversionSite c, MulExpr e, NumType sourceType, NumType destType
where 
  // e is nested inside c, with only parents that roughly "preserve" the value
  getRestrictedParent*(e) = c and
  // the destination type is wider than the type of the multiplication
  e.getType() = sourceType and
  c.getConversionTarget() = destType and
  destType.widerThan(sourceType) and
  // not a trivial conversion
  not c.isTrivial() and
  // not an explicit conversion, which is probably intended by a user
  c.isImplicit() and
  // not obviously small and ok
  not small(e) and
  e.getEnclosingCallable().fromSource()
select c, "$@ converted to "+ destType.getName() +" by use in " + ("a " + c.kind()).regexpReplaceAll("^a ([aeiou])", "an $1") + ".", e, sourceType.getName() + " multiplication"
