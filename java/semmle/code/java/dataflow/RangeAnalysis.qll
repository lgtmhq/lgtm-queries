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
 * A library for range analysis.
 *
 * Currently only supports a very limited set of guards and no actual
 * range inference besides constants.
 */

import java
import SSA
private import DefUse

/** An expression that always has the same integer value. */
pragma[nomagic]
private predicate constantIntegerExpr(Expr e, int val) {
  e.(CompileTimeConstantExpr).getIntValue() = val or
  exists(SsaDefinition ssa, LocalScopeVariable v, Expr src |
    e = ssa.getAUse(v) and
    src = ssa.getDefiningExpr(v).(VariableAssign).getSource() and
    constantIntegerExpr(src, val)
  )
}

/** An expression that always has the same integer value. */
class ConstantIntegerExpr extends Expr {
  ConstantIntegerExpr() {
    constantIntegerExpr(this, _)
  }

  /** Get the integer value of this expression. */
  int getIntValue() {
    constantIntegerExpr(this, result)
  }
}

/** An expression that might have the value `i`. */
private Expr exprWithIntValue(int i) {
  result.(ConstantIntegerExpr).getIntValue() = i or
  result.(ParExpr).getExpr() = exprWithIntValue(i) or
  result.(ConditionalExpr).getTrueExpr() = exprWithIntValue(i) or
  result.(ConditionalExpr).getFalseExpr() = exprWithIntValue(i)
}

/** A variable with a lower bound. */
private predicate incLoopVar(LocalScopeVariable v, int bound) {
  exists(SsaDefinition init |
    v instanceof LocalVariableDecl and
    init.getDefiningExpr(v).(VariableAssign).getSource().(ConstantIntegerExpr).getIntValue() = bound and
    forall(SsaDefinition ssa | ssa != init and ssa.isVariableUpdate(v) |
      exists(VariableUpdate update | ssa.getDefiningExpr(v) = update |
        update instanceof PreIncExpr or
        update instanceof PostIncExpr
      )
    )
  )
}

/** An `RValue` or a `MethodAccess`. */
class IntComparableExpr extends Expr {
  IntComparableExpr() {
    this instanceof RValue or this instanceof MethodAccess
  }

  /** An integer that is directly assigned to the expression in case of a variable; or zero. */
  int relevantInt() {
    exists(SsaDefinition ssa, LocalScopeVariable v |
      this.(RValue).getVariable() = v and
      ssa.getDefiningExpr(v).(VariableAssign).getSource() = exprWithIntValue(result)
    ) or
    result = 0
  }
}

/**
 * An expression that directly tests whether a given expression is equal to `k` or not.
 * The set of `k`s is restricted to those that are relevant for the expression or
 * have a direct comparison with the expression.
 *
 * If `result` evaluates to `branch`, then `e` is guaranteed to be equal to `k` if `is_k`
 * is true, and different from `k` if `is_k` is false.
 */
pragma[nomagic]
Expr integerGuard(IntComparableExpr e, boolean branch, int k, boolean is_k) {
  exists(EqualityTest eqtest, boolean polarity |
    eqtest = result and
    eqtest.hasOperands(e, any(ConstantIntegerExpr c | c.getIntValue() = k)) and
    polarity = eqtest.polarity() and
    (branch = true and is_k = polarity or branch = false and is_k = polarity.booleanNot())
  ) or
  exists(EqualityTest eqtest, int val |
    k = e.relevantInt() and
    eqtest = result and
    eqtest.hasOperands(e, any(ConstantIntegerExpr c | c.getIntValue() = val)) and
    is_k = false and
    k != val and
    branch = eqtest.polarity()
  ) or
  exists(ComparisonExpr comp, ConstantIntegerExpr c, int val |
    k = e.relevantInt() and
    comp = result and
    comp.hasOperands(e, c) and
    c.getIntValue() = val and
    is_k = false
    |
    comp.getLesser().getProperExpr() = c and comp.isStrict() and branch = true and val >= k or
    comp.getLesser().getProperExpr() = c and comp.isStrict() and branch = false and val < k or
    comp.getLesser().getProperExpr() = c and not comp.isStrict() and branch = true and val > k or
    comp.getLesser().getProperExpr() = c and not comp.isStrict() and branch = false and val <= k or
    comp.getGreater().getProperExpr() = c and comp.isStrict() and branch = true and val <= k or
    comp.getGreater().getProperExpr() = c and comp.isStrict() and branch = false and val > k or
    comp.getGreater().getProperExpr() = c and not comp.isStrict() and branch = true and val < k or
    comp.getGreater().getProperExpr() = c and not comp.isStrict() and branch = false and val >= k
  ) or
  exists(ComparisonExpr comp, LocalScopeVariable incloopvar, VarAccess va, int val |
    k = e.relevantInt() and
    comp = result and
    incLoopVar(incloopvar, val) and
    va = incloopvar.getAnAccess() and
    comp.hasOperands(e, va) and
    is_k = false
    |
    comp.getLesser().getProperExpr() = va and comp.isStrict() and branch = true and val >= k or
    comp.getLesser().getProperExpr() = va and not comp.isStrict() and branch = true and val > k
  )
}

/**
 * A guard that splits the values of a variable into one range with an upper bound of `k-1`
 * and one with a lower bound of `k`.
 *
 * If `branch_with_lower_bound_k` is true then `result` is equivalent to `k <= varaccess`
 * and if it is false then `result` is equivalent to `k > varaccess`.
 */
Expr intBoundGuard(RValue varaccess, boolean branch_with_lower_bound_k, int k) {
  exists(ComparisonExpr comp, ConstantIntegerExpr c, int val |
    comp = result and
    comp.hasOperands(varaccess, c) and
    c.getIntValue() = val and
    varaccess.getVariable().getType() instanceof IntegralType
    |
    comp.getLesser().getProperExpr() = c and comp.isStrict() and branch_with_lower_bound_k = true and val + 1 = k or // c < x
    comp.getLesser().getProperExpr() = c and not comp.isStrict() and branch_with_lower_bound_k = true and val = k or // c <= x
    comp.getGreater().getProperExpr() = c and comp.isStrict() and branch_with_lower_bound_k = false and val = k or // x < c
    comp.getGreater().getProperExpr() = c and not comp.isStrict() and branch_with_lower_bound_k = false and val + 1 = k // x <= c
  )
}

