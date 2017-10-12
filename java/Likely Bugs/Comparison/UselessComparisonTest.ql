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
 * @name Useless comparison test
 * @description A comparison operation that always evaluates to true or always
 *              evaluates to false may indicate faulty logic and may result in
 *              dead code.
 * @kind problem
 * @problem.severity warning
 * @precision very-high
 * @id java/constant-comparison
 * @tags correctness
 *       logic
 *       external/cwe/cwe-570
 *       external/cwe/cwe-571
 */
import semmle.code.java.dataflow.Guards
import semmle.code.java.dataflow.SSA
import semmle.code.java.dataflow.SignAnalysis
import semmle.code.java.dataflow.RangeAnalysis

/** Holds if `cond` always evaluates to `isTrue`. */
predicate constCond(BinaryExpr cond, boolean isTrue, Reason reason) {
  exists(ComparisonExpr comp, Expr lesser, Expr greater, Bound b, int d1, int d2, Reason r1, Reason r2 |
    comp = cond and
    lesser = comp.getLesserOperand() and
    greater = comp.getGreaterOperand() and
    bounded(lesser, b, d1, isTrue, r1) and
    bounded(greater, b, d2, isTrue.booleanNot(), r2) and
    (reason = r1 or reason = r2) and
    (r1 instanceof NoReason and r2 instanceof NoReason or not reason instanceof NoReason)
    |
    isTrue = true and comp.isStrict() and d1 < d2 or
    isTrue = true and not comp.isStrict() and d1 <= d2 or
    isTrue = false and comp.isStrict() and d1 >= d2 or
    isTrue = false and not comp.isStrict() and d1 > d2
  ) or
  exists(EqualityTest eq, Expr lhs, Expr rhs |
    eq = cond and
    lhs = eq.getLeftOperand() and
    rhs = eq.getRightOperand()
    |
    exists(Bound b, int d1, int d2, boolean upper, Reason r1, Reason r2 |
      bounded(lhs, b, d1, upper, r1) and
      bounded(rhs, b, d2, upper.booleanNot(), r2) and
      isTrue = eq.polarity().booleanNot() and
      (reason = r1 or reason = r2) and
      (r1 instanceof NoReason and r2 instanceof NoReason or not reason instanceof NoReason)
      |
      upper = true and d1 < d2 or // lhs <= b + d1 < b + d2 <= rhs
      upper = false and d1 > d2   // lhs >= b + d1 > b + d2 >= rhs
    ) or
    exists(Bound b, int d, Reason r1, Reason r2, Reason r3, Reason r4 |
      bounded(lhs, b, d, true, r1) and
      bounded(lhs, b, d, false, r2) and
      bounded(rhs, b, d, true, r3) and
      bounded(rhs, b, d, false, r4) and
      isTrue = eq.polarity()
      |
      (reason = r1 or reason = r2 or reason = r3 or reason = r4) and
      (r1 instanceof NoReason and r2 instanceof NoReason and r3 instanceof NoReason and r4 instanceof NoReason or
      not reason instanceof NoReason)
    )
  )
}

/** Holds if `cond` always evaluates to `isTrue`. */
predicate constCondSimple(BinaryExpr cond, boolean isTrue) {
  constCond(cond, isTrue, any(NoReason nr))
}

/** Gets a seemingly positive expression that might be negative due to overflow. */
Expr overFlowCand() {
  exists(BinaryExpr bin |
    result = bin and
    positive(bin.getLeftOperand()) and
    positive(bin.getRightOperand())
    |
    bin instanceof AddExpr or
    bin instanceof MulExpr or
    bin instanceof LShiftExpr
  ) or
  exists(AssignOp op |
    result = op and
    positive(op.getDest()) and
    positive(op.getRhs())
    |
    op instanceof AssignAddExpr or
    op instanceof AssignMulExpr or
    op instanceof AssignLShiftExpr
  ) or
  exists(AddExpr add, CompileTimeConstantExpr c |
    result = add and
    add.hasOperands(overFlowCand(), c) and
    c.getIntValue() >= 0
  ) or
  exists(AssignAddExpr add, CompileTimeConstantExpr c |
    result = add and
    add.getDest() = overFlowCand() and
    add.getRhs() = c and
    c.getIntValue() >= 0
  ) or
  exists(SsaExplicitUpdate x | result = x.getAUse() and x.getDefiningExpr() = overFlowCand()) or
  result.(ParExpr).getExpr() = overFlowCand() or
  result.(AssignExpr).getRhs() = overFlowCand() or
  result.(LocalVariableDeclExpr).getInit() = overFlowCand()
}

/** Gets an expression that equals `v` plus a positive value. */
Expr increaseOfVar(SsaVariable v) {
  exists(AssignAddExpr add |
    result = add and
    positive(add.getDest()) and
    add.getRhs() = v.getAUse()
  ) or
  exists(AddExpr add, Expr e |
    result = add and
    add.hasOperands(v.getAUse(), e) and
    positive(e)
  ) or
  exists(SsaExplicitUpdate x | result = x.getAUse() and x.getDefiningExpr() = increaseOfVar(v)) or
  result.(ParExpr).getExpr() = increaseOfVar(v) or
  result.(AssignExpr).getRhs() = increaseOfVar(v) or
  result.(LocalVariableDeclExpr).getInit() = increaseOfVar(v)
}

predicate overFlowTest(ComparisonExpr comp) {
  exists(SsaVariable v |
    comp.getLesserOperand() = increaseOfVar(v) and
    comp.getGreaterOperand() = v.getAUse()
  ) or
  comp.getLesserOperand() = overFlowCand() and
  comp.getGreaterOperand().(IntegerLiteral).getIntValue() = 0
}


/**
 * Holds if `test` and `guard` are equality tests of the same integral variable v with constants `c1` and `c2`.
 */
predicate guardedTest(EqualityTest test, EqualityTest guard, CompileTimeConstantExpr c1, CompileTimeConstantExpr c2) {
  exists(SsaVariable v | 
    guard.hasOperands(v.getAUse(), c1) and
    test.hasOperands(v.getAUse(), c2) and
    v.getSourceVariable().getType() instanceof IntegralType
  )
}

/**
 * Holds if `guard` implies that `test` always has the value `testIsTrue`.
 */
predicate uselessEqTest(EqualityTest test, boolean testIsTrue, EqualityTest guard) {
  exists(ConditionBlock cb, boolean guardIsTrue, CompileTimeConstantExpr c1, CompileTimeConstantExpr c2 |
    guardedTest(test, guard, c1, c2) and
    c1.getIntValue() = c2.getIntValue() and
    cb.getCondition() = guard and
    cb.controls(test.getBasicBlock(), guardIsTrue) and
    testIsTrue = guardIsTrue.booleanXor(guard.polarity().booleanXor(test.polarity()))
  )
}

from BinaryExpr test, boolean testIsTrue, string reason, Expr reasonElem
where
  (
    if uselessEqTest(test, _, _) then
      exists(EqualityTest r | uselessEqTest(test, testIsTrue, r) and reason = ", because of $@" and reasonElem = r)
    else if constCondSimple(test, _) then
      (constCondSimple(test, testIsTrue) and reason = "" and reasonElem = test) // dummy reason element
    else
      exists(CondReason r | constCond(test, testIsTrue, r) and reason = ", because of $@" and reasonElem = r.getCond())
  ) and
  not overFlowTest(test) and
  not exists(AssertStmt assert | assert.getExpr() = test.getParent*())
select test, "Test is always " + testIsTrue + reason + ".", reasonElem, "this condition"
