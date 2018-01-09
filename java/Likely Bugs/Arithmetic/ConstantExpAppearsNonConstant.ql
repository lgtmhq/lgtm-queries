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
 * @name Expression always evaluates to the same value
 * @description An expression that always evaluates to the same value, but which has a non-constant subexpression, indicates a mistake.
 * @kind problem
 * @problem.severity warning
 * @precision very-high
 * @id java/evaluation-to-constant
 * @tags maintainability
 *       useless-code
 */
import java

int integralTypeWidth (IntegralType t) {
  if (t.hasName("long") or t.hasName("Long"))
  then result = 64
  else result = 32
}

int eval (Expr e) {
  result = e.(CompileTimeConstantExpr).getIntValue()
}

predicate isConstantExp (Expr e) {
  // A literal is constant.
  e instanceof Literal
  or
  // A parenthesized expression is constant if its proper expression is.
  isConstantExp(e.(ParExpr).getProperExpr())
  or
  e instanceof TypeAccess
  or
  e instanceof ArrayTypeAccess
  or
  e instanceof WildcardTypeAccess
  or
  // A binary expression is constant if both its operands are.
  exists(BinaryExpr b | b = e |
    isConstantExp(b.getLeftOperand()) and
    isConstantExp(b.getRightOperand())
  )
  or
  // A cast expression is constant if its expression is.
  exists (CastExpr c | c = e | isConstantExp(c.getExpr().getProperExpr()))
  or
  // Multiplication by 0 is constant.
  exists (MulExpr m | m = e | eval(m.getAnOperand().getProperExpr()) = 0)
  or
  // Integer remainder by 1 is constant.
  exists (RemExpr r | r = e |
    r.getLeftOperand().getType() instanceof IntegralType and
    eval(r.getRightOperand().getProperExpr()) = 1
  )
  or
  // Left shift by 64 (longs) or 32 (all other integer types) is constant.
  exists (LShiftExpr s | s = e |
    exists (IntegralType t | t = s.getLeftOperand().getType() |
      eval(s.getRightOperand().getProperExpr()) = integralTypeWidth(t)
    )
  )
  or
  exists (AndBitwiseExpr a | a = e |
    eval(a.getAnOperand().getProperExpr()) = 0
  )
  or
  exists (AndLogicalExpr a | a = e |
    a.getAnOperand().getProperExpr().(BooleanLiteral).getBooleanValue() = false
  )
  or
  exists (OrLogicalExpr o | o = e |
    o.getAnOperand().getProperExpr().(BooleanLiteral).getBooleanValue() = true
  )
}

from Expr e
where isConstantExp(e)
  and exists(Expr child | e.getAChildExpr() = child |
        not isConstantExp(child) and
        not child instanceof Annotation
      )
  and not e instanceof CompileTimeConstantExpr
  // Exclude expressions that appear to be disabled deliberately (e.g. `false && ...`).
  and not e.(AndLogicalExpr).getAnOperand().(BooleanLiteral).getBooleanValue() = false
select e, "Expression always evaluates to the same value."
