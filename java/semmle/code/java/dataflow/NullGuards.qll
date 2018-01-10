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
 * Provides classes and predicates for null guards.
 */

import java
import SSA
private import Guards
private import DefUse
private import RangeUtils
private import IntegerGuards

/** An expression that is always `null`. */
Expr alwaysNullExpr() {
  result instanceof NullLiteral or
  result.(ParExpr).getExpr() = alwaysNullExpr() or
  result.(CastExpr).getExpr() = alwaysNullExpr()
}

/** An equality test between an expression `e` and an enum constant `c`. */
Expr enumConstEquality(Expr e, boolean polarity, EnumConstant c) {
  exists(EqualityTest eqtest |
    eqtest = result and
    eqtest.hasOperands(e, c.getAnAccess()) and
    polarity = eqtest.polarity()
  )
}

/** An expression that is provably not `null`. */
Expr clearlyNotNullExpr() {
  result instanceof ClassInstanceExpr or
  result instanceof ArrayCreationExpr or
  result instanceof TypeLiteral or
  result instanceof ThisAccess or
  result instanceof StringLiteral or
  result instanceof AddExpr and result.getType() instanceof TypeString or
  result.(ParExpr).getExpr() = clearlyNotNullExpr() or
  result.(CastExpr).getExpr() = clearlyNotNullExpr() or
  exists(ConditionalExpr c | c = result and c.getTrueExpr() = clearlyNotNullExpr() and c.getFalseExpr() = clearlyNotNullExpr()) or
  exists(ConditionBlock cond, SsaVariable v, boolean branch, RValue rval |
    cond.getCondition() = nullGuard(v, branch, false) and
    cond.controls(rval.getBasicBlock(), branch) and
    rval = v.getAUse() and
    result = rval
  ) or
  exists(SsaVariable v | clearlyNotNull(v) and result = v.getAUse())
}

/** An SSA variable that is provably not `null`. */
predicate clearlyNotNull(SsaVariable v) {
  exists(Expr src |
    src = v.(SsaExplicitUpdate).getDefiningExpr().(VariableAssign).getSource() and
    src = clearlyNotNullExpr()
  ) or
  exists(CatchClause cc |
    cc.getVariable() = v.(SsaExplicitUpdate).getDefiningExpr()
  ) or
  exists(SsaVariable captured |
    v.(SsaImplicitInit).captures(captured) and
    clearlyNotNull(captured)
  )
}

/**
 * An expression that directly tests whether a given expression, `e`, is null or not.
 *
 * If `result` evaluates to `branch`, then `e` is guaranteed to be null if `isnull`
 * is true, and non-null if `isnull` is false.
 */
Expr basicNullGuard(Expr e, boolean branch, boolean isnull) {
  exists(EqualityTest eqtest, boolean polarity |
    eqtest = result and
    eqtest.hasOperands(e, any(NullLiteral n)) and
    polarity = eqtest.polarity() and
    (branch = true and isnull = polarity or branch = false and isnull = polarity.booleanNot())
  ) or
  result.(InstanceOfExpr).getExpr() = e and branch = true and isnull = false or
  exists(MethodAccess call, Method m, boolean polarity |
    call = result and
    call.getAnArgument() = e and
    call.getMethod() = m and
    m.getDeclaringType().hasQualifiedName("java.util", "Objects") and
    (m.hasName("isNull") and polarity = true or m.hasName("nonNull") and polarity = false) and
    (branch = true and isnull = polarity or branch = false and isnull = polarity.booleanNot())
  ) or
  exists(MethodAccess call |
    call = result and
    call.getAnArgument() = e and
    call.getMethod() instanceof EqualsMethod and
    branch = true and
    isnull = false
  ) or
  exists(EqualityTest eqtest |
    eqtest = result and
    eqtest.hasOperands(e, clearlyNotNullExpr()) and
    isnull = false and
    branch = eqtest.polarity()
  ) or
  result = enumConstEquality(e, branch, _) and isnull = false or
  exists(MethodAccess call, Method m, int ix |
    call = result and
    call.getArgument(ix) = e and
    call.getMethod().getSourceDeclaration() = m and
    m = customNullGuard(ix, branch, isnull)
  )
}

/**
 * An expression that tests whether a given SSA variable is null or not.
 *
 * If `result` evaluates to `branch`, then `v` is guaranteed to be null if `isnull`
 * is true, and non-null if `isnull` is false.
 */
Expr nullGuard(SsaVariable v, boolean branch, boolean isnull) {
  result = basicNullGuard(sameValue(v, _), branch, isnull) or
  exists(SsaExplicitUpdate vbool, Expr boolinit |
    result = vbool.getAUse() and
    vbool.getDefiningExpr().(VariableAssign).getSource() = boolinit and
    boolinit = nullGuard(v, branch, isnull)
  ) or
  result.(AndBitwiseExpr).getAnOperand() = nullGuard(v, branch, isnull) and branch = true or
  result.(OrBitwiseExpr).getAnOperand() = nullGuard(v, branch, isnull) and branch = false or
  // Note that the following four cases are only relevant because `nullGuard` is used in contexts that are not `ConditionNode`s.
  result.(AndLogicalExpr).getAnOperand() = nullGuard(v, branch, isnull) and branch = true or
  result.(OrLogicalExpr).getAnOperand() = nullGuard(v, branch, isnull) and branch = false or
  result.(LogNotExpr).getExpr().getProperExpr() = nullGuard(v, branch.booleanNot(), isnull) or
  result.(ParExpr).getExpr().getProperExpr() = nullGuard(v, branch, isnull) or
  exists(EqualityTest eqtest, boolean branch0, boolean polarity, BooleanLiteral boollit |
    eqtest = result and
    eqtest.hasOperands(nullGuard(v, branch0, isnull), boollit) and
    eqtest.polarity() = polarity and
    branch = branch0.booleanXor(polarity).booleanXor(boollit.getBooleanValue())
  ) or
  exists(SsaExplicitUpdate v0, boolean branch1, ConditionalExpr c |
    // If `v0 = ng ? k : ...` or `v0 = ng ? ... : k` then a guard
    // proving `v0 != k` ensures that `ng` evaluates to `branch1`.  If `ng`
    // in turn is a null guard for `v` then the guard for `v0` also becomes
    // a null guard for `v`. The following two disjuncts handle the cases where
    // `k` is either null or an integer constant, respectively.
    v0.getDefiningExpr().(VariableAssign).getSource().getProperExpr() = c and
    c.getCondition() = nullGuard(v, branch1, isnull)
    |
    result = nullGuard(v0, branch, false) and
    (
      c.getTrueExpr() = alwaysNullExpr() and branch1 = false or
      c.getFalseExpr() = alwaysNullExpr() and branch1 = true
    ) or
    exists(int k |
      result = integerGuard(v0.getAUse(), branch, k, false)
      |
      c.getTrueExpr() = any(ConstantIntegerExpr c0 | c0.getIntValue() = k) and branch1 = false or
      c.getFalseExpr() = any(ConstantIntegerExpr c0 | c0.getIntValue() = k) and branch1 = true
    )
  )
}

/**
 * A return statement that on a return value of `retval` allows the conclusion that the
 * parameter `p` either is null or non-null as specified by `isnull`.
 */
private predicate validReturnInCustomNullGuard(ReturnStmt ret, Parameter p, boolean retval, boolean isnull) {
  exists(Method m |
    ret.getEnclosingCallable() = m and
    p.getCallable() = m and
    m.getReturnType().(PrimitiveType).hasName("boolean")
  ) and
  exists(SsaImplicitInit ssa | ssa.isParameterDefinition(p) |
    exists(ConditionBlock cond |
      // lifted to assist join ordering
      validReturnHelper(ret, ssa, cond, isnull) and
      (retval = true or retval = false)
    ) or
    exists(Expr res | res = ret.getResult() |
      res = nullGuard(ssa, retval, isnull)
    )
  )
}

private predicate validReturnHelper(ReturnStmt ret, SsaImplicitInit ssa, ConditionBlock cond, boolean isnull) {
  exists(boolean branch | 
    cond.controls(ret.getBasicBlock(), branch) and
    cond.getCondition() = nullGuard(ssa, branch, isnull)
  )
}

/**
 * A non-overridable method with a boolean return value that performs a null-check
 * on the `index`th parameter. A return value equal to `retval` allows us to conclude
 * that the argument either is null or non-null as specified by `isnull`.
 */
private Method customNullGuard(int index, boolean retval, boolean isnull) {
  exists(Parameter p |
    result.getReturnType().(PrimitiveType).hasName("boolean") and
    not result.isOverridable() and
    p.getCallable() = result and
    not p.isVarargs() and
    p.getType() instanceof RefType and
    p.getPosition() = index and
    forex(ReturnStmt ret |
      ret.getEnclosingCallable() = result and
      exists(Expr res | res = ret.getResult() | not res.(BooleanLiteral).getBooleanValue() = retval.booleanNot())
      |
      validReturnInCustomNullGuard(ret, p, retval, isnull)
    )
  )
}

/**
 * `guard` is a guard expression that suggests that `v` might be null.
 *
 * This is equivalent to `guard = basicNullGuard(sameValue(v, _), _, true)` but excludes custom
 * null guards, as they might be invoked solely for their side effects.
 */
predicate guardSuggestsVarMaybeNull(Expr guard, SsaVariable v) {
  guard = basicNullGuard(sameValue(v, _), _, true) and
  not guard.(MethodAccess).getMethod().getSourceDeclaration() = customNullGuard(_, _, true)
}
