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
 * Provides a class for handling variables in the data flow analysis.
 */
import cpp
private import semmle.code.cpp.controlflow.SSA
private import semmle.code.cpp.dataflow.internal.SubBasicBlocks

/**
 * A conceptual variable that is assigned only once, like an SSA variable. This
 * class is used for tracking data flow through variables, where the desired
 * semantics is sometimes different from what the SSA library provides. Unlike
 * SSA, there are no _phi_ nodes; instead, each `VariableAccess` may be
 * associated with more than one `FlowVar`.
 *
 * Each instance of this class corresponds to a modification or an initial
 * value of a variable. A `FlowVar` has exactly one result for either
 * `definedByExpr` or `definedByInitialValue`. The documentation on those two
 * member predicates explains how a `FlowVar` relates to syntactic constructs of
 * the language.
 */
cached class FlowVar extends TFlowVar {
  /**
   * Gets a `VariableAccess` that _may_ take its value from `this`. Consider
   * the following snippet.
   *
   * ```
   * int x = 0;
   * if (b) { f(x); x = 1; }
   * g(x)
   * ```
   *
   * The access to `x` in `f(x)` may take its value from the `FlowVar`
   * corresponding to `int x = 0`, while the access to `x` in `g(x)` may take
   * its value from the `FlowVar` corresponding to `int x = 0` or the `FlowVar`
   * corresponding to `x = 1`. The `x` in `x = 1` is not considered to be an
   * access.
   */
  cached abstract VariableAccess getAnAccess();

  /**
   * Holds if this `FlowVar` corresponds to a modification occurring when `node` is
   * evaluated, receiving a value best described by `e`. The following is an
   * exhaustive list of cases where this may happen.
   *
   * - `node` is an `Initializer` and `e` is its contained expression.
   * - `node` is an `AssignExpr`, and `e` is its right-hand side.
   * - `node` is an `AssignOperation`, and `e` is `node`.
   * - `node` is a `CrementOperation`, and `e` is `node`. The case where
   *   `node instanceof PostCrementOperation` is an exception to the rule that
   *   `this` contains the value of `e` after the evaluation of `node`.
   */
  cached abstract predicate definedByExpr(Expr e, ControlFlowNode node);

  /**
   * Holds if this `FlowVar` corresponds to the initial value of `v`. The following
   * is an exhaustive list of cases where this may happen.
   *
   * - `v` is a parameter, and `this` contains the value of the parameter at
   *   the entry point of its function body.
   * - `v` is an uninitialized local variable, and `v` contains its (arbitrary)
   *   value before it is reassigned. If it can be statically determined that a
   *   local variable is always overwritten before it is used, there is no
   *   `FlowVar` instance for the uninitialized value of that variable.
   */
  cached abstract predicate definedByInitialValue(LocalScopeVariable v);

  /** Gets a textual representation of this element. */
  cached abstract string toString();

  /** Gets the location of this element. */
  cached abstract Location getLocation();
}

private import FlowVar_internal

/**
 * Provides classes and predicates that ought to be private but cannot use the
 * `private` annotation because they may be referred to by unit tests.
 */
module FlowVar_internal {
  /**
   * For various reasons, not all variables handled perfectly by the SSA library.
   * Ideally, this predicate should become larger as the SSA library improves.
   * Before we can remove the `BlockVar` class completely, the SSA library needs
   * the following improvements.
   * - Considering uninitialized local variables to be definitions.
   * - Supporting fields, globals and statics like the Java SSA library does.
   * - Supporting all local variables, even if their address is taken by
   *   address-of, reference assignments, or lambdas.
   */
  predicate fullySupportedSsaVariable(Variable v) {
    v = any(SsaDefinition def).getAVariable() and
    // SSA variables do not exist before their first assignment, but one
    // feature of this data flow library is to track where uninitialized data
    // ends up.
    not mayBeUsedUninitialized(v, _) and
    // The SSA library has a theoretically accurate treatment of reference types,
    // treating them as immutable, but for data flow it gives better results in
    // practice to make the variable synonymous with its contents.
    not v.getType().getUnspecifiedType() instanceof ReferenceType
  }

  /**
   * Holds if `sbb` is the `SubBasicBlock` where `v` receives its initial value.
   * See the documentation for `FlowVar.definedByInitialValue`.
   */
  predicate blockVarDefinedByVariable(
      SubBasicBlock sbb, LocalScopeVariable v)
  {
    sbb = v.(Parameter).getFunction().getEntryPoint()
    or
    exists(DeclStmt declStmt |
      declStmt.getDeclaration(_) = v.(LocalVariable) and
      sbb.contains(declStmt) and
      mayBeUsedUninitialized(v, _)
    )
  }

  newtype TFlowVar =
    TSsaVar(SsaDefinition def, LocalScopeVariable v) {
      fullySupportedSsaVariable(v) and
      v = def.getAVariable()
    }
    or
    TBlockVar(SubBasicBlock sbb, Variable v) {
      not fullySupportedSsaVariable(v) and
      reachable(sbb) and
      (
        initializer(sbb.getANode(), v, _)
        or
        assignmentLikeOperation(sbb, v, _)
        or
        blockVarDefinedByVariable(sbb, v)
      )
    }

  /**
   * A variable whose analysis is backed by the SSA library.
   */
  class SsaVar extends TSsaVar, FlowVar {
    SsaDefinition def;
    LocalScopeVariable v;

    SsaVar() { this = TSsaVar(def, v) }

    override VariableAccess getAnAccess() {
      result = this.getAReachedSsaDefinition().getAUse(v)
    }

    override predicate definedByExpr(Expr e, ControlFlowNode node) {
      e = def.getDefiningValue(v) and
      (if def.getDefinition() = v.getInitializer().getExpr()
       then node = v.getInitializer()
       else node = def.getDefinition())
    }

    override predicate definedByInitialValue(LocalScopeVariable param) {
      def.definedByParameter(param) and
      param = v
    }

    private SsaDefinition getAReachedSsaDefinition() {
      def = result
      or
      getAReachedSsaDefinition() = result.getAPhiInput(v)
    }

    override string toString() { result = def.toString(v) }

    override Location getLocation() { result = def.getLocation() }
  }

  /**
   * A variable whose analysis is backed by a simple control flow analysis that
   * does not perform as well as the SSA library but gives better results for
   * data flow purposes in some cases.
   */
  class BlockVar extends TBlockVar, FlowVar {
    SubBasicBlock sbb;
    Variable v;

    BlockVar() { this = TBlockVar(sbb, v) }

    override VariableAccess getAnAccess() {
      result.getTarget() = v and
      result = this.getAReachedSBB().getANode() and
      not overwrite(result, _)
    }

    override predicate definedByInitialValue(LocalScopeVariable lsv) {
      blockVarDefinedByVariable(sbb, lsv) and
      lsv = v
    }

    override predicate definedByExpr(Expr e, ControlFlowNode node) {
      assignmentLikeOperation(node, v, e) and
      node = sbb
      or
      initializer(node, v, e) and
      node = sbb.getANode()
    }

    pragma[nomagic]
    private SubBasicBlock getAReachedSBB() {
      result = sbb
      or
      exists(SubBasicBlock mid |
        mid = this.getAReachedSBB() and
        result = mid.getASuccessor() and
        not assignmentLikeOperation(result, v, _)
      )
    }

    override string toString() {
      exists(Expr e |
        this.definedByExpr(e, _) and
        result = v +" := "+ e
      )
      or
      this.definedByInitialValue(_) and
      result = "initial value of "+ v
      or
      // impossible case
      not this.definedByExpr(_, _) and
      not this.definedByInitialValue(_) and
      result = "undefined "+ v
    }

    override Location getLocation() { result = sbb.getStart().getLocation() }
  }

  /**
   * A local variable that is uninitialized immediately after its declaration.
   */
  class UninitializedLocalVariable extends LocalVariable {
    UninitializedLocalVariable() {
      not this.hasInitializer() and
      not this.isStatic()
    }
  }

  /** Holds if `va` may be an uninitialized access to `v`. */
  predicate mayBeUsedUninitialized(UninitializedLocalVariable v, VariableAccess va) {
    exists(BasicBlock bb, int vaIndex |
      va.getTarget() = v and
      readAccess(va) and
      va = bb.getNode(vaIndex) and
      notAccessedAtStartOfBB(v, bb) and
      (
        vaIndex < indexOfFirstOverwriteInBB(v, bb)
        or
        not exists(indexOfFirstOverwriteInBB(v, bb))
      )
    )
  }

  /**
   * Holds if `v` has not been accessed at the start of `bb`, for a variable
   * `v` where `allReadsDominatedByOverwrite(v)` does not hold.
   */
  predicate notAccessedAtStartOfBB(UninitializedLocalVariable v, BasicBlock bb) {
    // Start from a BB containing an uninitialized variable
    bb.getANode().(DeclStmt).getDeclaration(_) = v and
    // Only consider variables for which initialization before reading cannot
    // be proved by simpler means. This predicate is expensive in time and
    // space, whereas `allReadsDominatedByOverwrite` is cheap.
    not allReadsDominatedByOverwrite(v)
    or
    exists(BasicBlock pred |
      pred = bb.getAPredecessor() and
      notAccessedAtStartOfBB(v, pred) and
      // Stop searching when `v` is accessed.
      not pred.getANode() = v.getAnAccess()
    )
  }

  /**
   * Holds if all read accesses of `v` are dominated by an overwrite of `v`.
   */
  predicate allReadsDominatedByOverwrite(UninitializedLocalVariable v) {
    forall(VariableAccess va |
      va.getTarget() = v and
      readAccess(va)
    | dominatedByOverwrite(v, va)
    )
  }

  /** Holds if `va` accesses `v` and is dominated by an overwrite of `v`. */
  predicate dominatedByOverwrite(UninitializedLocalVariable v,
                                 VariableAccess va)
  {
    exists(BasicBlock bb, int vaIndex |
      va = bb.getNode(vaIndex) and
      va.getTarget() = v
    | vaIndex > indexOfFirstOverwriteInBB(v, bb)
      or
      bbStrictlyDominates(getAnOverwritingBB(v), bb)
    )
  }

  /** Gets a basic block in which `v` is overwritten. */
  BasicBlock getAnOverwritingBB(UninitializedLocalVariable v) {
    exists(indexOfFirstOverwriteInBB(v, result))
  }

  int indexOfFirstOverwriteInBB(LocalVariable v, BasicBlock bb) {
    result = min(int i | overwrite(v.getAnAccess(), bb.getNode(i)))
  }

  /**
   * Holds if the value of the variable accessed at `va` may affect the execution
   * of the program.
   */
  predicate readAccess(VariableAccess va) {
    reachable(va) and
    not overwrite(va, _) and
    not va = any(SizeofExprOperator so).getAChild+() and
    not va = any(AlignofExprOperator ao).getAChild+()
  }

  /**
   * Holds if the value of the variable accessed at `va` is completely
   * overwritten at `node`, where `va` is uniquely determined by `node`.
   */
  predicate overwrite(VariableAccess va, ControlFlowNode node) {
    va = node.(AssignExpr).getLValue()
  }

  /**
   * Holds if `v` is modified as a side effect of evaluating `node`, receiving a
   * value best described by `e`. This corresponds to `FlowVar::definedByExpr`,
   * except that the case where `node instanceof Initializer` is covered by
   * `initializer` instead of this predicate.
   */
  predicate assignmentLikeOperation(
      ControlFlowNode node, Variable v, Expr assignedExpr)
  {
    // Together, the two following cases cover `Assignment`
    node = any(AssignExpr ae |
      v = ae.getLValue().(VariableAccess).getTarget() and
      assignedExpr = ae.getRValue()
    )
    or
    node = any(AssignOperation ao |
      v = ao.getLValue().(VariableAccess).getTarget() and
      // Here and in the `PrefixCrementOperation` case, we say that the assigned
      // expression is the operation itself. For example, we say that `x += 1`
      // assigns `x += 1` to `x`. The justification is that after this operation,
      // `x` will contain the same value that `x += 1` evaluated to.
      assignedExpr = ao
    )
    or
    // This case does not add further data flow paths, except if a
    // `PrefixCrementOperation` is itself a source
    node = any(CrementOperation op |
      v = op.getOperand().(VariableAccess).getTarget() and
      assignedExpr = op
    )
  }

  /**
   * Holds if `v` is initialized by `init` to have value `assignedExpr`.
   */
  predicate initializer(
      Initializer init, LocalVariable v, Expr assignedExpr)
  {
    v = init.getDeclaration() and
    assignedExpr = init.getExpr()
  }

  /**
   * A point in a basic block where a non-SSA variable may have a different value
   * than it did elsewhere in the same basic block. Extending this class
   * configures the `SubBasicBlocks` library as needed for the implementation of
   * this library.
   */
  class DataFlowSubBasicBlockCutNode extends SubBasicBlockCutNode {
    DataFlowSubBasicBlockCutNode() {
      exists(Variable v |
        not fullySupportedSsaVariable(v) and
        assignmentLikeOperation(this, v, _)
        // It is not necessary to cut the basic blocks at `Initializer` nodes
        // because the affected variable can have no _other_ value before its
        // initializer. It is not necessary to cut basic blocks at procedure
        // entries for the sake of `Parameter`s since we are already guaranteed
        // to have a `SubBasicBlock` starting at procedure entry.
      )
    }
  }
} /* module FlowVar_internal */
