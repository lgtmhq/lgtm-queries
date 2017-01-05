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
 * A library for nullness analysis.
 *
 * Local variables that may be null are tracked to see if they might reach
 * a dereference and cause a NullPointerException. Assertions are assumed to
 * hold, so results guarded by, for example, `assert x != null;` or
 * `if (x == null) { assert false; }` are excluded.
 */

/*
 * Implementation details:
 *
 * The three exported predicates, `nullDeref`, `alwaysNullDeref`, and
 * `superfluousNullGuard`, compute potential null dereferences, definite null
 * dereferences, and superfluous null checks, respectively.  The bulk of the
 * library supports `nullDeref`, while the latter two are fairly simple in
 * comparison.
 *
 * The NPE (NullPointerException) candidates are computed by
 * `nullDerefCandidate` and consist of three parts: A variable definition that
 * might be null as computed by `varMaybeNull`, a dereference that can cause a
 * NPE as computed by `firstVarDereferenceInBlock`, and a control flow path
 * between the two points.  The path is computed by `varMaybeNullInBlock`,
 * which is the transitive closure of the step relation `nullVarStep`
 * originating in a definition given by `varMaybeNull`.  The step relation
 * `nullVarStep` is essentially just the successor relation on basic blocks
 * restricted to exclude edges along which the variable cannot be null.
 *
 * The step relation `nullVarStep` is then reused twice to produce two
 * refinements of the path reachability predicate `varMaybeNullInBlock` in
 * order to prune impossible paths that would otherwise lead to a potential
 * NPE.  These two refinements are `varMaybeNullInBlock_corrCond` and
 * `varMaybeNullInBlock_trackVar` and are described in further detail below.
 */

import java
import SSA
private import Guards
private import DefUse
private import RangeAnalysis
private import NullGuards
private import semmle.code.java.Collections
private import semmle.code.java.frameworks.Assertions

/** An expression that may be `null`. */
private Expr nullExpr() {
  result instanceof NullLiteral or
  result.(ParExpr).getExpr() = nullExpr() or
  result.(ConditionalExpr).getTrueExpr() = nullExpr() or
  result.(ConditionalExpr).getFalseExpr() = nullExpr() or
  result.(AssignExpr).getSource() = nullExpr() or
  result.(CastExpr).getExpr() = nullExpr()
}

/** An expression of a boxed type that is implicitly unboxed. */
private predicate unboxed(Expr e) {
  e.getType() instanceof BoxedType and
  (
    exists(ArrayAccess aa | aa.getIndexExpr() = e) or
    exists(ArrayCreationExpr ace | ace.getADimension() = e) or
    exists(LocalVariableDeclExpr decl | decl.getVariable().getType() instanceof PrimitiveType and decl.getInit() = e) or
    exists(AssignExpr assign | assign.getDest().getType() instanceof PrimitiveType and assign.getSource() = e) or
    exists(AssignOp assign | assign.getSource() = e and assign.getType() instanceof PrimitiveType) or
    exists(EqualityTest eq | eq.getAnOperand() = e and eq.getAnOperand().getType() instanceof PrimitiveType) or
    exists(BinaryExpr bin | bin.getAnOperand() = e and not bin instanceof EqualityTest and bin.getType() instanceof PrimitiveType) or
    exists(UnaryExpr un | un.getExpr() = e) or
    exists(ConditionalExpr cond | cond.getType() instanceof PrimitiveType | cond.getTrueExpr() = e or cond.getFalseExpr() = e) or
    exists(ConditionNode cond | cond.getCondition() = e) or
    exists(Parameter p | p.getType() instanceof PrimitiveType and p.getAnArgument() = e) or
    exists(ReturnStmt ret | ret.getEnclosingCallable().getType() instanceof PrimitiveType and ret.getResult() = e)
  )
}

/** An expression that is being dereferenced. These are the points where `NullPointerException`s can occur. */
private predicate dereference(Expr e) {
  exists(EnhancedForStmt for | for.getExpr() = e) or
  exists(SynchronizedStmt synch | synch.getExpr() = e) or
  exists(FieldAccess fa, Field f | fa.getQualifier() = e and fa.getField() = f and not f.isStatic()) or
  exists(MethodAccess ma, Method m | ma.getQualifier() = e and ma.getMethod() = m and not m.isStatic()) or
  exists(ClassInstanceExpr cie | cie.getQualifier() = e) or
  exists(ArrayAccess aa | aa.getArray() = e) or
  exists(CastExpr cast | cast.getExpr() = e and e.getType() instanceof BoxedType and cast.getType() instanceof PrimitiveType) or
  unboxed(e)
}

/**
 * The `ControlFlowNode` in which the given SSA variable is being dereferenced.
 *
 * The `VarAccess` is included for nicer error reporting.
 */
private ControlFlowNode varDereference(SsaDefinition ssa, LocalScopeVariable v, VarAccess va) {
  exists(Expr e |
    dereference(e) and
    e = sameValue(ssa, v, va) and
    result = e.getProperExpr()
  )
}

/**
 * A `ControlFlowNode` that ensures that the SSA variable is not null in any
 * subsequent use, either by dereferencing it or by an assertion.
 */
private ControlFlowNode ensureNotNull(SsaDefinition ssa, LocalScopeVariable v) {
  result = varDereference(ssa, v, _) or
  result.(AssertStmt).getExpr() = nullGuard(ssa, v, true, false) or
  exists(AssertTrueMethod m | result = m.getACheck(nullGuard(ssa, v, true, false))) or
  exists(AssertFalseMethod m | result = m.getACheck(nullGuard(ssa, v, false, false))) or
  exists(AssertNotNullMethod m | result = m.getACheck(ssa.getAUse(v)))
}

/**
 * A variable dereference that cannot be reached by a `null` value, because of an earlier
 * dereference or assertion in the same `BasicBlock`.
 */
private predicate unreachableVarDereference(BasicBlock bb, SsaDefinition ssa, LocalScopeVariable v, ControlFlowNode varDeref) {
  exists(ControlFlowNode n, int i, int j |
    (n = ensureNotNull(ssa, v) or assertFail(bb, n)) and
    varDeref = varDereference(ssa, v, _) and
    bb.getNode(i) = n and
    bb.getNode(j) = varDeref and
    i < j
  )
}

/**
 * The first dereference of a variable in a given `BasicBlock` excluding those dereferences
 * that are preceded by a not-null assertion or a trivially failing assertion.
 */
private predicate firstVarDereferenceInBlock(BasicBlock bb, SsaDefinition ssa, LocalScopeVariable v, VarAccess va) {
  exists(ControlFlowNode n |
    varDereference(ssa, v, va) = n and
    n.getBasicBlock() = bb and
    not unreachableVarDereference(bb, ssa, v, n)
  )
}

/** A variable suspected of being `null`. */
private predicate varMaybeNull(SsaDefinition ssa, LocalScopeVariable v) {
  // A variable compared to null might be null.
  exists(Expr e |
    guardSuggestsVarMaybeNull(e, ssa, v) and
    not ssa.isPhiNode(v) and
    not clearlyNotNull(ssa, v) and
    // Comparisons in finally blocks are excluded since missing exception edges in the CFG could otherwise yield FPs.
    not exists(TryStmt try |
      try.getFinally() = e.getEnclosingStmt().getParent*()
    ) and
    (
      exists(ConditionalExpr c | c.getCondition().getAChildExpr*() = e) or
      not exists(MethodAccess ma |
        ma.getAnArgument().getAChildExpr*() = e
      )
    )
  ) or
  // A parameter might be null if there is a null argument somewhere.
  exists(Parameter p, Expr arg |
    p = v and
    ssa.isParameterDefinition(p) and
    p.getAnArgument() = arg and
    arg = nullExpr() and
    not arg.getEnclosingCallable() instanceof TestMethod
  ) or
  // If the source of a variable is null then the variable may be null.
  ssa.getDefiningExpr(v).(VariableAssign).getSource() = nullExpr()
}

/** An array or collection that contains at least one element. */
private Expr nonEmptyExpr() {
  // An array creation with a known positive size is trivially non-empty.
  result.(ArrayCreationExpr).getFirstDimensionSize() > 0 or
  exists(SsaDefinition ssa, LocalScopeVariable v |
    // A use of an array variable is non-empty if...
    result = ssa.getAUse(v) and
    v.getType() instanceof Array
    |
    // ...its definition is non-empty...
    ssa.getDefiningExpr(v).(VariableAssign).getSource() = nonEmptyExpr() or
    // ...or it is guarded by a condition proving its length to be non-zero.
    exists(ConditionBlock cond, boolean branch, FieldAccess length |
      cond.controls(result.getBasicBlock(), branch) and
      cond.getCondition() = integerGuard(length, branch, 0, false) and
      length.getField().hasName("length") and
      length.getQualifier() = ssa.getAUse(v)
    )
  ) or
  exists(SsaDefinition ssa, LocalScopeVariable v |
    // A use of a Collection variable is non-empty if...
    result = ssa.getAUse(v) and
    v.getType() instanceof CollectionType and
    exists(ConditionBlock cond, boolean branch, Expr c |
      // ...it is guarded by a condition...
      cond.controls(result.getBasicBlock(), branch) and
      // ...and it isn't modified in the scope of the condition...
      forall(MethodAccess ma, Method m |
        m = ma.getMethod() and
        ma.getQualifier().(VarAccess).getVariable() = v and
        cond.controls(ma.getBasicBlock(), branch)
        |
        m instanceof CollectionQueryMethod
      ) and
      cond.getCondition() = c
      |
      // ...and the condition proves that it is non-empty, either by using the `isEmpty` method...
      c.(MethodAccess).getMethod().hasName("isEmpty") and branch = false and c.(MethodAccess).getQualifier() = ssa.getAUse(v) or
      // ...or a check on its `size`.
      exists(MethodAccess size |
        c = integerGuard(size, branch, 0, false) and
        size.getMethod().hasName("size") and
        size.getQualifier() = ssa.getAUse(v)
      )
    )
  )
}

/** The control flow edge that exits an enhanced for loop if the `Iterable` is empty. */
private predicate enhancedForEarlyExit(EnhancedForStmt for, ControlFlowNode n1, ControlFlowNode n2) {
  exists(Expr forExpr |
    n1.getANormalSuccessor() = n2 and
    for.getExpr() = forExpr and
    forExpr.getAChildExpr*() = n1 and
    not forExpr.getAChildExpr*() = n2 and
    n1.getANormalSuccessor() = for.getVariable() and
    not n2 = for.getVariable()
  )
}

/** A control flow edge that cannot be taken. */
private predicate impossibleEdge(BasicBlock bb1, BasicBlock bb2) {
  exists(EnhancedForStmt for |
    enhancedForEarlyExit(for, bb1.getANode(), bb2.getANode()) and
    for.getExpr() = nonEmptyExpr()
  )
}

/** A control flow edge that leaves a finally-block. */
private predicate leavingFinally(BasicBlock bb1, BasicBlock bb2, boolean normaledge) {
  exists(TryStmt try, Block finally |
    try.getFinally() = finally and
    bb1.getABBSuccessor() = bb2 and
    bb1.getEnclosingStmt().getParent*() = finally and
    not bb2.getEnclosingStmt().getParent*() = finally and
    if bb1.getLastNode().getANormalSuccessor() = bb2.getFirstNode() then normaledge = true else normaledge = false
  )
}

/**
 * The step relation for propagating that a given SSA variable might be `null` in a given `BasicBlock`.
 *
 * If `(midssa,v)` is null in `mid` then `(ssa,v)` might be null in `bb`.
 *
 * A boolean flag tracks whether a non-normal completion is waiting to resume upon the exit of a finally-block.
 * If the flag is set, then the normal edge out of the finally-block is prohibited, but if it is not set then
 * no knowledge is assumed of any potentially waiting completions. `midstoredcompletion` is the flag before
 * the step and `storedcompletion` is the flag after the step.
 */
private predicate nullVarStep(SsaDefinition midssa, LocalScopeVariable v, BasicBlock mid, boolean midstoredcompletion, SsaDefinition ssa, BasicBlock bb, boolean storedcompletion) {
  varMaybeNull(_, v) and
  (midstoredcompletion = true or midstoredcompletion = false) and
  midssa.isLiveAtEndOfBlock(v, mid) and
  (ssa.getAPhiInput(v) = midssa and ssa.getBasicBlock() = bb or ssa = midssa and not exists(SsaDefinition phi | phi.isPhiNode(v) and phi.getBasicBlock() = bb)) and
  not ensureNotNull(midssa, v).getBasicBlock() = mid and
  not assertFail(mid, _) and
  bb = mid.getABBSuccessor() and
  not impossibleEdge(mid, bb) and
  not exists(ConditionBlock cond, boolean branch |
    cond = mid and
    cond.getTestSuccessor(branch) = bb and
    cond.getCondition() = nullGuard(midssa, v, branch, false)
  ) and
  not (leavingFinally(mid, bb, true) and midstoredcompletion = true) and
  if bb.getFirstNode() = any(TryStmt try | | try.getFinally()) then
    (if bb.getFirstNode() = mid.getLastNode().getANormalSuccessor() then storedcompletion = false else storedcompletion = true)
  else if leavingFinally(mid, bb, _) then
    storedcompletion = false
  else
    storedcompletion = midstoredcompletion
}

/**
 * The transitive closure of `nullVarStep` originating from `varMaybeNull`. That is, those `BasicBlock`s
 * for which the SSA variable is suspected of being `null`.
 */
private predicate varMaybeNullInBlock(SsaDefinition ssa, LocalScopeVariable v, BasicBlock bb, boolean storedcompletion) {
  varMaybeNull(ssa, v) and bb = ssa.getBasicBlock() and storedcompletion = false or
  exists(BasicBlock mid, SsaDefinition midssa, boolean midstoredcompletion |
    varMaybeNullInBlock(midssa, v, mid, midstoredcompletion) and
    nullVarStep(midssa, v, mid, midstoredcompletion, ssa, bb, storedcompletion)
  )
}

/**
 * A potential `null` dereference. That is, the first dereference of a variable in a block
 * where it is suspected of being `null`.
 */
private predicate nullDerefCandidate(LocalScopeVariable v, VarAccess va) {
  exists(SsaDefinition ssa, BasicBlock bb |
    firstVarDereferenceInBlock(bb, ssa, v, va) and
    varMaybeNullInBlock(ssa, v, bb, _)
  )
}

/*
 * In the following, the potential `null` dereference candidates are pruned by proving that
 * a `NullPointerException` (NPE) cannot occur. This is done by pruning the control-flow paths
 * that lead to the NPE candidate in two ways:
 *
 * 1. For each set of correlated conditions that are passed by the path, consistent
 *    branches must be taken. For example, the following code is safe due to the two tests on
 *    `flag` begin correlated.
 *    ```
 *    x = null;
 *    if (flag) x = new A();
 *    if (flag) x.m();
 *    ```
 *
 * 2. For each other variable that changes its value alongside the potential NPE candidate,
 *    the passed conditions must be consistent with its value. For example, the following
 *    code is safe due to the value of `t`.
 *    ```
 *    x = null;
 *    t = null;
 *    if (...) { x = new A(); t = new B(); }
 *    if (t != null) x.m();
 *    ```
 *    We call such a variable a _tracking variable_ as it tracks the null-ness of `x`.
 */

/** A variable that is assigned `null` if the given condition takes the given branch. */
private predicate varConditionallyNull(SsaDefinition ssa, LocalScopeVariable v, ConditionBlock cond, boolean branch) {
  exists(ConditionalExpr condexpr |
    ssa.getDefiningExpr(v).(VariableAssign).getSource().getProperExpr() = condexpr and
    condexpr.getCondition().getProperExpr() = cond.getCondition()
    |
    condexpr.getTrueExpr() = nullExpr() and branch = true and not condexpr.getFalseExpr() = nullExpr() or
    condexpr.getFalseExpr() = nullExpr() and branch = false and not condexpr.getTrueExpr() = nullExpr()
  )
  or
  ssa.getDefiningExpr(v).(VariableAssign).getSource() = nullExpr() and
  cond.controls(ssa.getBasicBlock(), branch)
}

/**
 * A condition that might be useful in proving an NPE candidate safe.
 *
 * This is a condition along the path that found the NPE candidate.
 */
private predicate interestingCond(LocalScopeVariable npecand, ConditionBlock cond) {
  nullDerefCandidate(npecand, _) and
  (varMaybeNullInBlock(_, npecand, cond, _) or varConditionallyNull(_, npecand, cond, _)) and
  not cond.getCondition().getAChildExpr*() = npecand.getAnAccess()
}

/** A pair of correlated conditions for a given NPE candidate. */
private predicate correlatedConditions(LocalScopeVariable npecand, ConditionBlock cond1, ConditionBlock cond2, boolean inverted) {
  interestingCond(npecand, cond1) and
  interestingCond(npecand, cond2) and
  cond1 != cond2 and
  cond1.getLocation().getStartLine() <= cond2.getLocation().getStartLine() and
  (
    exists(SsaDefinition ssa, LocalScopeVariable v |
      cond1.getCondition() = ssa.getAUse(v) and
      cond2.getCondition() = ssa.getAUse(v) and
      inverted = false
    ) or
    exists(SsaDefinition ssa, LocalScopeVariable v, boolean branch1, boolean branch2 |
      cond1.getCondition() = nullGuard(ssa, v, branch1, true) and
      cond1.getCondition() = nullGuard(ssa, v, branch1.booleanNot(), false) and
      cond2.getCondition() = nullGuard(ssa, v, branch2, true) and
      cond2.getCondition() = nullGuard(ssa, v, branch2.booleanNot(), false) and
      inverted = branch1.booleanXor(branch2)
    ) or
    exists(SsaDefinition ssa, LocalScopeVariable v, RValue rv1, RValue rv2, int k, boolean branch1, boolean branch2 |
      rv1 = ssa.getAUse(v) and
      rv2 = ssa.getAUse(v) and
      cond1.getCondition() = integerGuard(rv1, branch1, k, true) and
      cond1.getCondition() = integerGuard(rv1, branch1.booleanNot(), k, false) and
      cond2.getCondition() = integerGuard(rv2, branch2, k, true) and
      cond2.getCondition() = integerGuard(rv2, branch2.booleanNot(), k, false) and
      inverted = branch1.booleanXor(branch2)
    ) or
    exists(SsaDefinition ssa, LocalScopeVariable v, int k, boolean branch1, boolean branch2 |
      cond1.getCondition() = intBoundGuard(ssa.getAUse(v), branch1, k) and
      cond2.getCondition() = intBoundGuard(ssa.getAUse(v), branch2, k) and
      inverted = branch1.booleanXor(branch2)
    ) or
    exists(SsaDefinition ssa, LocalScopeVariable v, EnumConstant c, boolean pol1, boolean pol2 |
      cond1.getCondition() = enumConstEquality(ssa.getAUse(v), pol1, c) and
      cond2.getCondition() = enumConstEquality(ssa.getAUse(v), pol2, c) and
      inverted = pol1.booleanXor(pol2)
    ) or
    exists(Field f |
      f.isFinal() and
      cond1.getCondition() = f.getAnAccess() and
      cond2.getCondition() = f.getAnAccess() and
      inverted = false
    )
  )
}

/** The state value after passing through a given branch of one of the conditions in the correlated pair. */
newtype ConditionState =
  FstCondIs(boolean branch) { branch = true or branch = false } or
  SndCondIs(boolean branch) { branch = true or branch = false } or
  InitialCondState()

/**
 * This is again the transitive closure of `nullVarStep` similarly to `varMaybeNullInBlock`, but
 * this time restricted based on a given pair of correlated conditions. The `state` argument tracks
 * whether a condition was passed through and what branch was taken.
 */
private predicate varMaybeNullInBlock_corrCond(SsaDefinition ssa, LocalScopeVariable v, BasicBlock bb, boolean storedcompletion, ConditionBlock cond1, ConditionBlock cond2, boolean inverted, ConditionState state) {
  nullDerefCandidate(v, _) and correlatedConditions(v, cond1, cond2, inverted) and
  (
    exists(boolean branch | varConditionallyNull(ssa, v, cond1, branch) and state = FstCondIs(branch)) or
    exists(boolean branch | varConditionallyNull(ssa, v, cond2, branch) and state = SndCondIs(branch)) or
    not varConditionallyNull(ssa, v, cond1, _) and not varConditionallyNull(ssa, v, cond2, _) and state = InitialCondState()
  ) and
  varMaybeNull(ssa, v) and bb = ssa.getBasicBlock() and storedcompletion = false or
  exists(BasicBlock mid, SsaDefinition midssa, boolean midstoredcompletion, ConditionState midstate |
    varMaybeNullInBlock_corrCond(midssa, v, mid, midstoredcompletion, cond1, cond2, inverted, midstate) and
    (
      cond1 = mid and exists(boolean branch | cond1.getTestSuccessor(branch) = bb and midstate = InitialCondState() and state = FstCondIs(branch)) or
      cond1 = mid and exists(boolean branch | cond1.getTestSuccessor(branch) = bb and midstate = state and state = SndCondIs(branch.booleanXor(inverted))) or
      cond2 = mid and exists(boolean branch | cond2.getTestSuccessor(branch) = bb and midstate = InitialCondState() and state = SndCondIs(branch)) or
      cond2 = mid and exists(boolean branch | cond2.getTestSuccessor(branch) = bb and midstate = state and state = FstCondIs(branch.booleanXor(inverted))) or
      cond1 != mid and cond2 != mid and state = midstate
    ) and
    nullVarStep(midssa, v, mid, midstoredcompletion, ssa, bb, storedcompletion)
  )
}

/*
 * A tracking variable has its possible values divided into two sets, A and B, for
 * which we can attribute at least one direct assignment to be contained in either
 * A or B.
 * Four kinds are supported:
 * - null: A means null and B means non-null.
 * - boolean: A means true and B means false.
 * - enum: A means a specific enum constant and B means any other value.
 * - int: A means a specific integer value and B means any other value.
 */

newtype TrackVarKind =
  TrackVarKindNull() or
  TrackVarKindBool() or
  TrackVarKindEnum() or
  TrackVarKindInt()

/** A variable that might be relevant as a tracking variable for the NPE candidate. */
private predicate trackingVar(LocalScopeVariable npecand, SsaDefinition trackssa, LocalScopeVariable trackvar, TrackVarKind kind, Expr init) {
  exists(ConditionBlock cond |
    interestingCond(npecand, cond) and
    varMaybeNullInBlock(_, npecand, cond, _) and
    cond.getCondition().getAChildExpr*() = trackvar.getAnAccess() and
    trackssa.getDefiningExpr(trackvar).(VariableAssign).getSource() = init
    |
    init instanceof NullLiteral and kind = TrackVarKindNull() or
    init = clearlyNotNullExpr() and kind = TrackVarKindNull() or
    init instanceof BooleanLiteral and kind = TrackVarKindBool() or
    init.(VarAccess).getVariable() instanceof EnumConstant and kind = TrackVarKindEnum() or
    exists(init.(ConstantIntegerExpr).getIntValue()) and kind = TrackVarKindInt()
  )
}

/** An expression that tests the value of a given tracking variable. */
private Expr trackingVarGuard(SsaDefinition trackssa, LocalScopeVariable trackvar, TrackVarKind kind, boolean branch, boolean isA) {
  exists(Expr init | trackingVar(_, trackssa, trackvar, kind, init) |
    result = basicNullGuard(trackvar.getAnAccess(), branch, isA) and kind = TrackVarKindNull() or
    result = trackvar.getAnAccess() and kind = TrackVarKindBool() and (branch = true or branch = false) and isA = branch or
    exists(boolean polarity, EnumConstant c, EnumConstant initc |
      initc.getAnAccess() = init and
      kind = TrackVarKindEnum() and
      result = enumConstEquality(trackvar.getAnAccess(), polarity, c) and
      (
        initc = c and branch = polarity.booleanNot() and isA = false or
        initc = c and branch = polarity and isA = true or
        initc != c and branch = polarity and isA = false
      )
    ) or
    exists(int k |
      init.(ConstantIntegerExpr).getIntValue() = k and
      kind = TrackVarKindInt()
      |
      result = integerGuard(trackvar.getAnAccess(), branch, k, isA) or
      exists(int k2 |
        result = integerGuard(trackvar.getAnAccess(), branch.booleanNot(), k2, true) and
        isA = false and
        k2 != k
      ) or
      exists(int bound, boolean branch_with_lower_bound |
        result = intBoundGuard(trackvar.getAnAccess(), branch_with_lower_bound, bound) and
        isA = false
        |
        branch = branch_with_lower_bound and k < bound or
        branch = branch_with_lower_bound.booleanNot() and bound <= k
      )
    )
  ) or
  exists(EqualityTest eqtest, boolean branch0, boolean polarity, BooleanLiteral boollit |
    eqtest = result and
    eqtest.hasOperands(trackingVarGuard(trackssa, trackvar, kind, branch0, isA), boollit) and
    eqtest.polarity() = polarity and
    branch = branch0.booleanXor(polarity).booleanXor(boollit.getBooleanValue())
  )
}

/** An update to a tracking variable that is contained fully in either A or B. */
private predicate isReset(SsaDefinition trackssa, LocalScopeVariable trackvar, TrackVarKind kind, SsaDefinition update, boolean isA) {
  exists(Expr init, Expr e |
    trackingVar(_, trackssa, trackvar, kind, init) and
    e = update.getDefiningExpr(trackvar).(VariableAssign).getSource()
    |
    e instanceof NullLiteral and kind = TrackVarKindNull() and isA = true or
    e = clearlyNotNullExpr() and kind = TrackVarKindNull() and isA = false or
    e.(BooleanLiteral).getBooleanValue() = isA and kind = TrackVarKindBool() or
    e.(VarAccess).getVariable().(EnumConstant) = init.(VarAccess).getVariable() and kind = TrackVarKindEnum() and isA = true or
    e.(VarAccess).getVariable().(EnumConstant) != init.(VarAccess).getVariable() and kind = TrackVarKindEnum() and isA = false or
    e.(ConstantIntegerExpr).getIntValue() = init.(ConstantIntegerExpr).getIntValue() and kind = TrackVarKindInt() and isA = true or
    e.(ConstantIntegerExpr).getIntValue() != init.(ConstantIntegerExpr).getIntValue() and kind = TrackVarKindInt() and isA = false
  )
}

/** The abstract value of the tracked variable. */
newtype TrackedValue =
  TrackedValueA() or
  TrackedValueB() or
  TrackedValueUnknown()

private TrackedValue trackValAorB(boolean isA) { isA = true and result = TrackedValueA() or isA = false and result = TrackedValueB() }

/** A control flow edge passing through a condition that implies a specific value for a tracking variable. */
private predicate stepImplies(BasicBlock bb1, BasicBlock bb2, SsaDefinition trackssa, LocalScopeVariable trackvar, TrackVarKind kind, boolean isA) {
  exists(ConditionBlock cond, boolean branch |
    cond = bb1 and
    cond.getTestSuccessor(branch) = bb2 and
    cond.getCondition() = trackingVarGuard(trackssa, trackvar, kind, branch, isA)
  )
}

/**
 * This is again the transitive closure of `nullVarStep` similarly to `varMaybeNullInBlock`, but
 * this time restricted based on a tracking variable.
 */
private predicate varMaybeNullInBlock_trackVar(SsaDefinition ssa, LocalScopeVariable v, BasicBlock bb, boolean storedcompletion, SsaDefinition trackssa, LocalScopeVariable trackvar, TrackVarKind kind, TrackedValue trackvalue) {
  nullDerefCandidate(v, _) and trackingVar(v, trackssa, trackvar, kind, _) and
  (
    exists(SsaDefinition init, boolean isA |
      init.isLiveAtEndOfBlock(trackvar, bb) and
      isReset(trackssa, trackvar, kind, init, isA) and trackvalue = trackValAorB(isA)
    ) or
    trackvalue = TrackedValueUnknown() and
    not exists(SsaDefinition init |
      init.isLiveAtEndOfBlock(trackvar, bb) and
      isReset(trackssa, trackvar, kind, init, _)
    )
  ) and
  varMaybeNull(ssa, v) and bb = ssa.getBasicBlock() and storedcompletion = false
  or
  exists(BasicBlock mid, SsaDefinition midssa, boolean midstoredcompletion, TrackedValue trackvalue0 |
    varMaybeNullInBlock_trackVar(midssa, v, mid, midstoredcompletion, trackssa, trackvar, kind, trackvalue0) and
    nullVarStep(midssa, v, mid, midstoredcompletion, ssa, bb, storedcompletion) and
    (
      trackvalue0 = TrackedValueUnknown() or
      // A step that implies a value that contradicts the current value is not allowed.
      exists(boolean isA | trackvalue0 = trackValAorB(isA) |
        not stepImplies(mid, bb, trackssa, trackvar, kind, isA.booleanNot())
      )
    ) and
    (
      // If no update occurs then the tracked value is unchanged unless the step implies a given value via a condition.
      not exists(SsaDefinition update |
        update.getBasicBlock() = bb and update.isVariableUpdate(trackvar)
      ) and
      (
        exists(boolean isA | stepImplies(mid, bb, trackssa, trackvar, kind, isA) | trackvalue = trackValAorB(isA)) or
        not stepImplies(mid, bb, trackssa, trackvar, kind, _) and trackvalue = trackvalue0
      )
      or
      // If an update occurs then the tracked value is set accordingly.
      exists(SsaDefinition update |
        update.getBasicBlock() = bb and update.isVariableUpdate(trackvar) |
        exists(boolean isA | isReset(trackssa, trackvar, kind, update, isA) | trackvalue = trackValAorB(isA)) or
        not isReset(trackssa, trackvar, kind, update, _) and trackvalue = TrackedValueUnknown()
      )
    )
  )
}

/**
 * A potential `null` dereference that has not been proven safe.
 */
predicate nullDeref(LocalScopeVariable v, VarAccess va) {
  nullDerefCandidate(v, va) and
  exists(SsaDefinition ssa, BasicBlock bb |
    firstVarDereferenceInBlock(bb, ssa, v, va) and
    forall(ConditionBlock cond1, ConditionBlock cond2, boolean inverted |
      correlatedConditions(v, cond1, cond2, inverted) |
      varMaybeNullInBlock_corrCond(ssa, v, bb, _, cond1, cond2, inverted, _)
    ) and
    forall(SsaDefinition guardssa, LocalScopeVariable guardvar, TrackVarKind kind |
      trackingVar(v, guardssa, guardvar, kind, _) |
      varMaybeNullInBlock_trackVar(ssa, v, bb, _, guardssa, guardvar, kind, _)
    )
  )
}

/**
 * A dereference of a variable that is always `null`.
 */
predicate alwaysNullDeref(LocalScopeVariable v, VarAccess va) {
  exists(BasicBlock bb, SsaDefinition ssa |
    forall(SsaDefinition def | def = ssa.getAnUltimateDefinition(v) |
      def.getDefiningExpr(v).(VariableAssign).getSource() = alwaysNullExpr()
    ) or
    exists(ConditionBlock cond, boolean branch |
      cond.controls(bb, branch) and
      cond.getCondition() = nullGuard(ssa, v, branch, true) and
      not clearlyNotNull(ssa, v)
    )
    |
    firstVarDereferenceInBlock(bb, ssa, v, va) and
    not exists(ConditionBlock cond, boolean branch |
      cond.controls(bb, branch) and
      cond.getCondition() = nullGuard(ssa, v, branch, false)
    )
  )
}

/** A `null` test on a variable that is not `null`. */
Expr superfluousNullGuard(SsaDefinition ssa, LocalScopeVariable v) {
  guardSuggestsVarMaybeNull(result, ssa, v) and
  (result instanceof EqualityTest or result instanceof MethodAccess) and
  not exists(TryStmt try |
    try.getFinally() = result.getEnclosingStmt().getParent*()
  ) and
  clearlyNotNull(ssa, v)
}

