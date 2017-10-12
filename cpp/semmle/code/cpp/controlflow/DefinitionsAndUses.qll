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

import default
private import semmle.code.cpp.controlflow.LocalScopeVariableReachability

/**
 * Computed relation: A "definition-use-pair" for a particular variable.
 * Intuitively, this means that `def` is an assignment to `var`, and
 * `use` is a read of `var` at which the value assigned by `def` may
 * be read. (There can be more than one definition reaching a single
 * use, and a single definition can reach many uses.)
 */
predicate definitionUsePair(LocalScopeVariable var, Expr def, Expr use) {
  exists(Use u |
    u = use
    and
    def.(Def).reaches(true, var, u)
    and
    u.getVariable(false) = var
  )
}

/**
 * Holds if the definition `def` of some stack variable can reach `node`, which
 * is a definition or use, without crossing definitions of the same variable.
 */
predicate definitionReaches(Expr def, Expr node) {
  def.(Def).reaches(true, _, (DefOrUse)node)
}

private predicate hasAddressOfAccess(LocalScopeVariable var) {
  exists(VariableAccess va | va.getTarget() = var | va.isAddressOfAccess())
}

/**
 * A use/use pair is a pair of uses of a particular variable `var`
 * where the same value might be read (meaning that there is a
 * control-flow path from `first` to `second` without crossing
 * a definition of `var`).
 */
predicate useUsePair(LocalScopeVariable var, Expr first, Expr second) {
  (
    /* If the address of `var` is used anywhere, we require that
     * a definition of `var` can reach the first use. This is to
     * rule out examples such as this:
     * ```
     * int x = 0;
     * int& y = x;
     * use(x);
     * y = 1;
     * use(x); // not a use-use pair with the use above
     * ```
     */
    hasAddressOfAccess(var)
    implies
    definitionUsePair(var, _, first)
  )
  and
  exists(Use u |
    u = second
    and
    first.(Use).reaches(false, var, u)
    and
    u.getVariable(false) = var
  )
}

/**
 * Holds if `va` is a use of the parameter `p` that could
 * observe the passed-in value.
 */
predicate parameterUsePair(Parameter p, VariableAccess va) {
  not parameterIsOverwritten(_, p) and va.getTarget() = p
  or
  exists(ParameterDef pd | pd.reaches(true, p, (Use)va))
}

/**
 * Utility class: A definition or use of a stack variable.
 */
library
class DefOrUse extends @cfgnode {
  /**
   * Gets the target variable of this definition or use.
   *
   * The `isDef` parameter is needed in order to ensure disjointness
   * of definitions and uses; in a variable initialization such as
   * `int x = y`, `y` is both a definition of `x`, as well as a use of
   * `y`, and `isDef` is used to distinguish the two situations.
   */
  abstract LocalScopeVariable getVariable(boolean isDef);

  pragma[noinline]
  private predicate reaches_helper(boolean isDef, LocalScopeVariable v, BasicBlock bb, int i) {
    getVariable(isDef) = v and
    bb.getNode(i) = this
  }

  /**
   * Holds if the value of `v` in this control-flow node reaches
   * `defOrUse` along some control-flow path without crossing a
   * definition of `v`.
   */
  cached
  predicate reaches(boolean isDef, LocalScopeVariable v, DefOrUse defOrUse) {
    /* Implementation detail: this predicate and its private auxiliary
     * predicates are instances of the more general predicates in
     * LocalScopeVariableReachability.qll, and should be kept in sync.
     *
     * Unfortunately, caching of abstract predicates does not work well, so the
     * predicates are duplicated for now.
     */
    exists(BasicBlock bb, int i |
      reaches_helper(isDef, v, bb, i) |
      exists(int j |
        j > i
        and
        (bbDefAt(bb, j, v, defOrUse) or bbUseAt(bb, j, v, defOrUse))
        and
        not exists(int k | firstBarrierAfterThis(isDef, k, v) and k < j)
      )
      or
      not firstBarrierAfterThis(isDef, _, v) and
      bbSuccessorEntryReachesDefOrUse(bb, v, defOrUse, _)
    )
  }

  private predicate firstBarrierAfterThis(boolean isDef, int j, LocalScopeVariable v) {
    exists(BasicBlock bb, int i |
      getVariable(isDef) = v
      and
      bb.getNode(i) = this
      and
      j = min(int k | bbBarrierAt(bb, k, v, _) and k > i)
    )
  }

  /** Gets a textual representation of this element. */
  string toString() { result = "DefOrUse" }
}

library
class Def extends DefOrUse {
  Def() {
    definition(_, this)
  }

  override LocalScopeVariable getVariable(boolean isDef) {
    definition(result, this) and isDef = true
  }
}

/** Holds if parameter `p` is potentially overwritten in the body of `f`. */
private predicate parameterIsOverwritten(Function f, Parameter p) {
  f.getAParameter() = p and
  definitionBarrier(p, _)
}

library
class ParameterDef extends DefOrUse {
  ParameterDef() {
    // Optimization: parameters that are not overwritten do not require
    // reachability analysis
    exists(Function f | parameterIsOverwritten(f, _) | this = f.getEntryPoint())
  }

  override LocalScopeVariable getVariable(boolean isDef) {
    exists(Function f | parameterIsOverwritten(f, result) | this = f.getEntryPoint())
    and
    isDef = true
  }
}

library
class Use extends DefOrUse {
  Use() {
    useOfVar(_, this)
  }

  override LocalScopeVariable getVariable(boolean isDef) {
    useOfVar(result, this) and isDef = false
  }
}

private predicate bbUseAt(BasicBlock bb, int i, LocalScopeVariable v, Use use) {
  bb.getNode(i) = use
  and
  use.getVariable(false) = v
}

private predicate bbDefAt(BasicBlock bb, int i, LocalScopeVariable v, Def def) {
  bb.getNode(i) = def
  and
  def.getVariable(true) = v
}

private predicate bbBarrierAt(BasicBlock bb, int i, LocalScopeVariable v, ControlFlowNode node) {
  bb.getNode(i) = node
  and
  definitionBarrier(v, node)
}

/**
 * Holds if the entry node of a _successor_ of basic block `bb` can
 * reach `defOrUse` without going through a barrier for `v`.
 * `defOrUse` may either be in the successor block, or in another
 * basic block reachable from the successor.
 *
 * `skipsFirstLoopAlwaysTrueUponEntry` indicates whether the first loop
 * on the path to `defOrUse` (if any), where the condition is provably
 * true upon entry, is skipped (including the step from `bb` to the
 * successor).
 */
private predicate bbSuccessorEntryReachesDefOrUse(BasicBlock bb, LocalScopeVariable v, DefOrUse defOrUse, boolean skipsFirstLoopAlwaysTrueUponEntry) {
  exists(BasicBlock succ, boolean succSkipsFirstLoopAlwaysTrueUponEntry |
    bbSuccessorEntryReachesLoopInvariant(bb, succ, skipsFirstLoopAlwaysTrueUponEntry, succSkipsFirstLoopAlwaysTrueUponEntry) |
    bbEntryReachesDefOrUseLocally(succ, v, defOrUse) and
    succSkipsFirstLoopAlwaysTrueUponEntry = false
    or
    not bbBarrierAt(succ, _, v, _) and
    bbSuccessorEntryReachesDefOrUse(succ, v, defOrUse, succSkipsFirstLoopAlwaysTrueUponEntry)
  )
}

private predicate bbEntryReachesDefOrUseLocally(BasicBlock bb, LocalScopeVariable v, DefOrUse defOrUse) {
  exists(int n |
    bbDefAt(bb, n, v, defOrUse) or bbUseAt(bb, n, v, defOrUse) |
    not exists(int m | m < n | bbBarrierAt(bb, m, v, _))
  )
}

/**
 * Holds if `barrier` is either a (potential) definition of `v` or follows an
 * access that gets the address of `v`. In both cases, the value of
 * `v` after `barrier` cannot be assumed to be the same as before.
 */
predicate definitionBarrier(LocalScopeVariable v, ControlFlowNode barrier) {
  definition(v, barrier)
  or
  exists(VariableAccess va |
    /* `va = barrier` does not work, as that could generate an
     * incorrect use-use pair (a barrier must exist _between_
     * uses):
     * ```
     * x = 0;
     * int& y = x; // use1
     * y = 1;
     * use(x); // use2
     * ```
     */
    va.getASuccessor() = barrier and
    va.getTarget() = v and
    va.isAddressOfAccess() and
    not exists(Call c | c.passesByReference(_, va)) // handled in definitionByReference
  )
}

/**
 * Holds if `def` is a (potential) assignment to stack variable `v`. That is,
 * the variable may hold another value in the control-flow node(s)
 * following `def` than before.
 */
predicate definition(LocalScopeVariable v, Expr def) {
  def = v.getInitializer().getExpr()
  or
  exists(Assignment assign |
    def = assign and
    assign.getLValue() = v.getAnAccess())
  or
  exists(CrementOperation crem |
    def = crem and
    crem.getOperand() = v.getAnAccess())
  or
  definitionByReference(v.getAnAccess(), def)
}

/**
 * Holds if `def` is a (definite) assignment to the stack variable `v`. `e` is
 * the assigned expression.
 */
predicate exprDefinition(LocalScopeVariable v, ControlFlowNode def, Expr e) {
  (
    def = v.getInitializer().getExpr() and
    def = e and
    not v.getType() instanceof ReferenceType
  )
  or
  exists(AssignExpr assign |
    def = assign and
    assign.getLValue() = v.getAnAccess() and
    e = assign.getRValue()
  )
}

/**
 * Holds if `def` is a variable passed by reference (as `va`) where the callee
 * (potentially) assigns the relevant parameter.
 *
 * All library functions except `std::move` are assumed to assign
 * call-by-reference parameters, and source code functions are assumed to
 * assign call-by-reference parameters that are accessed somewhere within the
 * function. The latter is an over-approximation, but avoids having to take
 * aliasing of the parameter into account.
 */
predicate definitionByReference(VariableAccess va, Expr def) {
  exists(Call c, int i |
    c.passesByReference(i, va)
    and
    def = c.getArgument(i)
    and
    forall(Function f |
      f = c.getTarget() and f.hasEntryPoint() |
      exists(f.getParameter(i).getAnAccess())
      or
      f.isVarargs() and i >= f.getNumberOfParameters()
      or
      // If the callee contains an AsmStmt, then it is better to
      // be conservative and assume that the parameter can be
      // modified.
      exists(AsmStmt stmt | stmt.getEnclosingFunction() = f)
    ) and
    not (
      c.getTarget().getNamespace().getName() = "std" and
      c.getTarget().getName() = "move"
    )
  )
  or
  // Extractor artifact when using templates; an expression call where the
  // target expression is an unknown literal. Since we cannot know what
  // these calls represent, assume they assign all their arguments
  exists(ExprCall c, Literal l |
    l = c.getExpr() and
    c.getAnArgument() = va and
    not exists(l.getValue()) and
    def = va
  )
}

private predicate accessInSizeof(VariableAccess use) {
  use.getParent+() instanceof SizeofOperator
}

/**
 * Holds if `use` is a non-definition use of stack variable `v`. This will not
 * include accesses on the LHS of an assignment (which don't retrieve the
 * variable value), but _will_ include accesses in increment/decrement
 * operations.
 */
predicate useOfVar(LocalScopeVariable v, VariableAccess use) {
  use = v.getAnAccess() and
  not exists(AssignExpr e | e.getLValue() = use) and
  not definitionByReference(use, _) and
  // sizeof accesses are resolved at compile-time
  not accessInSizeof(use)
}

/**
 * Same as `useOfVar(v, use)`, but with the extra condition that the
 * access `use` actually reads the value of the stack variable `v` at
 * run-time. (Non-examples include `&x` and function calls where the
 * callee does not use the relevant parameter.)
 */
predicate useOfVarActual(LocalScopeVariable v, VariableAccess use) {
  useOfVar(v, use) and
  not use.isAddressOfAccess() and
  // A call to a function that does not use the relevant parameter
  not exists(Call c, int i |
    c.getArgument(i) = use and
    c.getTarget().hasEntryPoint() and
    not exists(c.getTarget().getParameter(i).getAnAccess())
  )
}
