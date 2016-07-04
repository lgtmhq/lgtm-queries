// Copyright 2016 Semmle Ltd.
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
 * Library for computing expression-level intra-procedural control flow graphs.
 *
 * The only API exported by this library are the toplevel classes `ControlFlowNode`
 * and its subclass `ConditionNode`, which wrap the successor relation and the
 * concept of true- and false-successors of conditions. A cfg node may either be a
 * statement, an expression, or the enclosing callable, indicating that
 * execution of the callable terminates.
 */

/*
 * The implementation is centered around the concept of a _completion_, which
 * models how the execution of a statement or expression terminates. There are five kinds of
 * completions: normal completion, `return` completion, `break` completion,
 * `continue` completion, and `throw` completion.
 *
 * Normal completions are further subdivided into boolean completions and all
 * other normal completions. A boolean completion adds the information that the
 * cfg node terminated with the given boolean value due to a subexpression
 * terminating with the other given boolean value. This is only
 * relevant for conditional contexts in which the value controls the
 * control-flow successor.
 *
 * Completions can be represented as an algebraic data type `Completion`
 *
 * ```
 * data Completion =
 *     Normal
 *   | Return
 *   | Boolean (boolean, boolean)
 *   | Break (Maybe Label)
 *   | Continue (Maybe Label)
 *   | Throw ThrownType
 * ```
 *
 * where `Label` is a statement label, and `ThrownType` is an exception type.
 *
 * Since QL does not yet support algebraic datatypes, we have to encode completions
 * as integers as follows:
 *
 *   - `Normal` is mapped to `-1`;
 *   - `Return` is mapped to `-2`;
 *   - `Boolean (true, true)` is mapped to `-3`;
 *   - `Boolean (true, false)` is mapped to `-4`;
 *   - `Boolean (false, true)` is mapped to `-5`;
 *   - `Boolean (false, false)` is mapped to `-6`;
 *   - `Break l` is mapped to `3*i`, where `i` encodes `l`;
 *   - `Continue l` is mapped to `3*i+1`, where `i` encodes `l`;
 *   - `Throw t` is mapped to `3*i+2`, where `i` encodes `t`.
 *
 * This encoding should be considered an implementation detail, which may
 * change without notice.
 *
 * The CFG is built by structural recursion over the AST. To achieve this the
 * CFG edges related to a given AST node, `n`, is divided into three categories:
 *   1. The in-going edge that points to the first CFG node to execute when the
 *      `n` is going to be executed.
 *   2. The out-going edges for control-flow leaving `n` that are going to some
 *      other node in the surrounding context of `n`.
 *   3. The edges that have both of their end-points entirely within the AST
 *      node and its children.
 * The edges in (1) and (2) are inherently non-local and are therefore
 * initially calculated as half-edges, that is, the single node, `k`, of the
 * edge contained within `n`, by the predicates `k = first(n)` and
 * `last(n, k, _)`, respectively. The edges in (3) can then be enumerated
 * directly by the predicate `succ` by calling `first` and `last` recursively
 * on the children of `n` and connecting the end-points. This yields the entire
 * CFG, since all edges are in (3) for _some_ AST node.
 *
 * The third parameter of `last` is the completion, which is necessary to
 * distinguish the out-going edges from `n`. Note that the completion changes
 * as the calculation of `last` proceeds outward through the AST; for example,
 * a `breakCompletion` is caught up by its surrounding loop and turned into a
 * `normalCompletion`, or a `normalCompletion` proceeds outward through the end
 * of a `finally` block and is turned into whatever completion was caught by
 * the `finally`, or a `booleanCompletion(false, _)` occurs in a loop condition
 * and is turned into a `normalCompletion` of the entire loop. When the edge is
 * eventually connected we use the completion at that level of the AST as the
 * label of the edge, thus creating an edge-labelled CFG.
 *
 * An important goal of the CFG is to get the order of side-effects correct.
 * Most expressions can have side-effects and must therefore be modelled in the
 * CFG in AST post-order. For example, a `MethodAccess` evaluates its arguments
 * before the call. Most statements don't have side-effects, but merely affect
 * the control-flow and some could therefore be excluded from the CFG. However,
 * as a design choice, all statements are included in the CFG and generally
 * serve as their own entry-points, thus executing in some version of AST
 * pre-order. A few notable exceptions are `ReturnStmt`, `ThrowStmt`,
 * `SynchronizedStmt`, `ThisConstructorInvocationStmt`, and
 * `SuperConstructorInvocationStmt`, which all have side-effects and therefore
 * are modelled in side-effect order. Loop statement nodes are only passed on
 * entry, after which control goes back and forth between body and loop
 * condition.
 *
 * Some out-going edges from boolean expressions have a known value and in some
 * contexts this affects the possible successors. For example, in `if(A || B)`
 * a short-circuit edge that skips `B` must be true and can therefore only lead
 * to the then-branch. If the `||` is modelled in post-order then this
 * information is lost, and consequently it is better to model `||` and `&&` in
 * pre-order. The conditional expression `? :` is also modelled in pre-order to
 * achieve consistent CFGs for the equivalent `A && B` and `A ? B : false`.
 * Finally, the logical negation is also modelled in pre-order to achieve
 * consistent CFGs for the equivalent `!(A || B)` and `!A && !B`. The boolean
 * value `b` is tracked with the completion `booleanCompletion(b, _)`.
 *
 * Note that the second parameter in a `booleanCompletion` isn't needed to
 * calculate the CFG. It is, however, needed to track the value of the
 * sub-expression. For example, this ensures that the false-successor of the
 * `ConditionNode` `A` in `if(!(A && B))` can be correctly identified as the
 * then-branch (even though this completion turns into a
 * `booleanCompletion(true, _)` from the perspective of the `if`-node).
 *
 * As a final note, expressions that aren't actually executed in the usual
 * sense are excluded from the CFG. This covers, for example, parentheses,
 * l-values that aren't r-values as well, and expressions in `ConstCase`s.
 * For example, the `x` in `x=3` is not in the CFG, but the `x` in `x+=3` is.
 */

import java

/** A node in the expression-level control-flow graph. */
class ControlFlowNode extends Top, @exprparent {
  /** The statement containing this node, if any. */
  Stmt getEnclosingStmt() {
    result = this or
    result = this.(Expr).getEnclosingStmt()
  }

  /** An immediate successor of this node. */
  ControlFlowNode getASuccessor() {
    result = succ(this)
  }

  /** An immediate predecessor of this node. */
  ControlFlowNode getAPredecessor() {
    this = succ(result)
  }

  /** An exception successor of this node. */
  ControlFlowNode getAnExceptionSuccessor() {
    result = succ(this, throwCompletion(_))
  }

  BasicBlock getBasicBlock() {
    result.getANode() = this
  }
}

/**
 * A string that is used as a statement label.
 */
private predicate label(string l) {
  exists (LabeledStmt lbl | l = lbl.getLabel())
}

/**
 * Assign unique (1-based) IDs to statement labels.
 */
private int labelId(string l) {
  l = rank[result](string ll | label(ll) | ll)
}

/**
 * Assign unique (1-based) IDs to exception types.
 */
private int throwableId(ThrowableType tt) {
  tt.getQualifiedName() = rank[result](ThrowableType ttt | | ttt.getQualifiedName())
}

/**
 * A completion indicating that a statement finished executing
 * without influencing control flow.
 */
private int normalCompletion()                     { result = -1 }

/**
 * A completion indicating that a `return` statement was encountered.
 */
private int returnCompletion()                     { result = -2 }

/**
 * A completion indicating that an unlabeled `break` statement was encountered.
 */
private int anonymousBreakCompletion()             { result = 0 }

/**
 * A completion indicating that a labeled `break` statement was encountered.
 */
private int labelledBreakCompletion(string lbl)    { result = 3*labelId(lbl) }

/**
 * A completion indicating that an unlabeled `continue` statement was encountered.
 */
private int anonymousContinueCompletion()          { result = 1 }

/**
 * A completion indicating that a labeled `continue` statement was encountered.
 */
private int labelledContinueCompletion(string lbl) { result = 3*labelId(lbl) + 1 }

/**
 * A completion indicating that a `throw` statement or a call that may throw
 * an exception was encountered.
 */
private int throwCompletion(ThrowableType tt)      { result = 3*throwableId(tt) + 2 }

/**
 * A completion indicating that a boolean expression finished executing
 * with the result `outervalue` and that the last subexpression to execute
 * finished with the result `innervalue`.
 *
 * For example, `!true` finishes with the completion `booleanCompletion(false, true)`.
 */
private int booleanCompletion(boolean outervalue, boolean innervalue) {
  result = -3 and outervalue = true and innervalue = true or
  result = -4 and outervalue = true and innervalue = false or
  result = -5 and outervalue = false and innervalue = true or
  result = -6 and outervalue = false and innervalue = false
}

/** The completion `booleanCompletion(value, value)`. */
private int basicBooleanCompletion(boolean value) {
  result = booleanCompletion(value, value)
}

/**
 * Get a label that applies to this statement.
 */
private string getLabel(Stmt s) {
  exists (LabeledStmt l | s = l.getStmt() |
    result = l.getLabel() or
    result = getLabel(l)
  )
}

/**
 * A throwable that's a (reflexive, transitive) supertype of an unchecked
 * exception. Besides the unchecked exceptions themselves, this includes
 * `java.lang.Throwable` and `java.lang.Exception`.
 */
library class UncheckedThrowableSuperType extends RefType {
  UncheckedThrowableSuperType() {
    this instanceof TypeThrowable or
    this instanceof TypeException or
    this instanceof UncheckedThrowableType
  }

  /** An unchecked throwable that is a subtype of this `UncheckedThrowableSuperType` and
   * sits as high as possible in the type hierarchy. This is mostly unique except for
   * `TypeThrowable` which results in both `TypeError` and `TypeRuntimeException`.
   */
  UncheckedThrowableType getAnUncheckedSubtype() {
    result = (UncheckedThrowableType)this or
    result instanceof TypeError and this instanceof TypeThrowable or
    result instanceof TypeRuntimeException and (this instanceof TypeThrowable or this instanceof TypeException)
  }
}

/**
 * Bind `t` to an exception type that may be thrown during execution of `n`,
 * either because `n` is a `throw` statement or because it is a call
 * that may throw an exception.
 */
private predicate mayThrow(ControlFlowNode n, ThrowableType t) {
  t = n.(ThrowStmt).getThrownExceptionType() or
  exists (Call c | c = n |
    t = c.getCallee().getAThrownExceptionType() or
    uncheckedExceptionFromCatch(n.getEnclosingStmt(), t)
  )
}

/**
 * Bind `t` to all unchecked exceptions that may be caught by some
 * `try-catch` inside which `s` is nested.
 */
private predicate uncheckedExceptionFromCatch(Stmt s, ThrowableType t) {
  exists (TryStmt try, UncheckedThrowableSuperType caught |
    t = caught.getAnUncheckedSubtype() and
    (s.getParent+() = try.getBlock() or s = try.getAResourceDecl()) and
    try.getACatchClause().getACaughtType() = caught
  )
}

/**
 * Get an exception type that may be thrown during execution of the
 * body or the resource declarations (if any) of `try`.
 */
private ThrowableType thrownInBody(TryStmt try) {
  exists (ControlFlowNode n, Stmt s | mayThrow(n, result) and s = n.getEnclosingStmt() |
    s.getParent+() = try.getBlock() or
    s = try.getAResourceDecl()
  )
}

/**
 * Bind `thrown` to an exception type that may be thrown during execution
 * of the body or the resource declarations of the `try` block to which
 * `c` belongs, such that `c` definitely catches that exception (if no
 * prior catch clause handles it).
 */
private predicate mustCatch(CatchClause c, ThrowableType thrown) {
  thrown = thrownInBody(c.getTry()) and
  hasSubtypeStar(c.getACaughtType(), thrown)
}

/**
 * Bind `thrown` to an exception type that may be thrown during execution
 * of the body or the resource declarations of the `try` block to which
 * `c` belongs, such that `c` may _not_ catch that exception.
 *
 * This predicate computes the complement of `mustCatch` over those
 * exception types that are thrown in the body/resource declarations of
 * the corresponding `try`.
 */
private predicate mayNotCatch(CatchClause c, ThrowableType thrown) {
  thrown = thrownInBody(c.getTry()) and
  not hasSubtypeStar(c.getACaughtType(), thrown)
}

/**
 * Bind `thrown` to an exception type that may be thrown during execution
 * of the body or the resource declarations of the `try` block to which
 * `c` belongs, such that `c` possibly catches that exception.
 */
private predicate mayCatch(CatchClause c, ThrowableType thrown) {
  mustCatch(c, thrown) or
  mayNotCatch(c, thrown) and exists(c.getACaughtType().commonSubtype(thrown))
}

/**
 * Given an exception type `thrown`, determine which catch clauses of
 * `try` may possibly catch that exception.
 */
private CatchClause handlingCatchClause(TryStmt try, ThrowableType thrown) {
  exists (int i | result = try.getCatchClause(i) |
    mayCatch(result, thrown) and
    not exists (int j | j < i | mustCatch(try.getCatchClause(j), thrown))
  )
}

/**
 * Boolean expressions that occur in a context in which their value affect control flow.
 * That is, contexts where the control-flow edges depend on `value` given that `b` ends
 * with a `booleanCompletion(value, _)`.
 */
private predicate inBooleanContext(Expr b) {
  exists (LogicExpr logexpr |
    logexpr.(BinaryExpr).getLeftOperand() = b or
    // Cannot use LogicExpr.getAnOperand or BinaryExpr.getAnOperand as they remove parentheses.
    logexpr.(BinaryExpr).getRightOperand() = b and inBooleanContext(logexpr) or
    logexpr.(UnaryExpr).getExpr() = b and inBooleanContext(logexpr)
  )
  or
  exists (ParExpr parexpr |
    parexpr.getExpr() = b and inBooleanContext(parexpr)
  )
  or
  exists (ConditionalExpr condexpr |
    condexpr.getCondition() = b or
    (condexpr.getTrueExpr() = b or condexpr.getFalseExpr() = b) and inBooleanContext(condexpr)
  )
  or
  exists (ConditionalStmt condstmt |
    condstmt.getCondition() = b
  )
}

/**
 * Expressions and statements with CFG edges in post-order AST traversal.
 *
 * This includes most expressions, except those that initiate or propagate branching control
 * flow (`LogicExpr`, `ConditionalExpr`), and parentheses, which aren't in the CFG.
 * Only a few statements are included; those with specific side-effects
 * occurring after the evaluation of their children, that is, `Call`, `ReturnStmt`,
 * and `ThrowStmt`. CFG nodes without child nodes in the CFG that may complete
 * normally are also included.
 */
library
class PostOrderNode extends ControlFlowNode {
  PostOrderNode() {
    // For VarAccess and ArrayAccess only read accesses (r-values) are included,
    // as write accesses aren't included in the CFG.
    this instanceof ArrayAccess and not exists (AssignExpr a | this = a.getDest()) or
    this instanceof ArrayCreationExpr or
    this instanceof ArrayInit or
    this instanceof Assignment or
    this instanceof BinaryExpr and not this instanceof LogicExpr or
    this instanceof UnaryExpr and not this instanceof LogNotExpr or
    this instanceof CastExpr or
    this instanceof InstanceOfExpr or
    this instanceof LocalVariableDeclExpr or
    this instanceof RValue or
    this instanceof Call or // includes both expressions and statements
    this instanceof ReturnStmt or
    this instanceof ThrowStmt or
    this instanceof Literal or
    this instanceof TypeLiteral or
    this instanceof ThisAccess or
    this instanceof SuperAccess or
    this.(Block).getNumStmt() = 0 or
    this instanceof SwitchCase or
    this instanceof EmptyStmt or
    this instanceof LocalClassDeclStmt or
    this instanceof AssertStmt // currently treated as a leaf node - i.e. its sub-expression(s) are excluded from the CFG
  }

  /** Get child nodes in their order of execution. Indexing starts at either -1 or 0. */
  ControlFlowNode getChildNode(int index) {
    exists (ArrayAccess e | e = this |
      index = 0 and result = e.getArray() or
      index = 1 and result = e.getIndexExpr()
    ) or
    exists (ArrayCreationExpr e | e = this |
      result = e.getDimension(index) or
      index = count(e.getADimension()) and result = e.getInit()
    ) or
    result = this.(ArrayInit).getInit(index) and index >= 0 or
    exists (AssignExpr e, ArrayAccess lhs | e = this and lhs = e.getDest() |
      index = 0 and result = lhs.getArray() or
      index = 1 and result = lhs.getIndexExpr() or
      index = 2 and result = e.getSource()
    ) or
    exists (AssignExpr e, VarAccess lhs | e = this and lhs = e.getDest() |
      index = -1 and result = lhs.getQualifier() and not result instanceof TypeAccess or
      index = 0 and result = e.getSource()
    ) or
    exists (AssignOp e | e = this |
      index = 0 and result = e.getDest() or
      index = 1 and result = e.getRhs()
    ) or
    exists (BinaryExpr e | e = this |
      index = 0 and result = e.getLeftOperand() or
      index = 1 and result = e.getRightOperand()
    ) or
    index = 0 and result = this.(UnaryExpr).getExpr() or
    index = 0 and result = this.(CastExpr).getExpr() or
    index = 0 and result = this.(InstanceOfExpr).getExpr() or
    index = 0 and result = this.(LocalVariableDeclExpr).getInit() or
    index = 0 and result = this.(RValue).getQualifier() and not result instanceof TypeAccess or
    exists (Call e | e = this |
      index = -1 and result = e.getQualifier() and not result instanceof TypeAccess or
      result = e.getArgument(index)
    ) or
    index = 0 and result = this.(ReturnStmt).getResult() or
    index = 0 and result = this.(ThrowStmt).getExpr()
  }

  /** The first child node, if any. */
  ControlFlowNode firstChild() {
    result = getChildNode(-1) or
    result = getChildNode(0) and not exists(getChildNode(-1))
  }

  /** Whether this CFG node has any child nodes. */
  predicate isLeafNode() {
    not exists(getChildNode(_))
  }

  /** Whether this node can finish with a `normalCompletion`. */
  predicate mayCompleteNormally() {
    not this instanceof BooleanLiteral and
    not this instanceof ReturnStmt and
    not this instanceof ThrowStmt
  }
}

/**
 * If the body of `loop` finishes with `completion`, the loop will
 * continue executing (provided the loop condition still holds).
 */
private predicate continues(int completion, LoopStmt loop) {
  completion = normalCompletion() or
  // only consider continue completions if there actually is a `continue`
  // somewhere inside this loop; we don't particularly care whether that
  // `continue` could actually target this loop, we just want to restrict
  // the size of the predicate
  exists (ContinueStmt cnt | cnt.getParent+() = loop |
    completion = anonymousContinueCompletion() or
    completion = labelledContinueCompletion(getLabel(loop))
  )
}

/**
 * Determine the part of the AST node `n` that will be executed first.
 */
private ControlFlowNode first(ControlFlowNode n) {
  result = n and n instanceof LogicExpr or
  result = n and n instanceof ConditionalExpr or
  result = n and n.(PostOrderNode).isLeafNode() or
  result = first(n.(PostOrderNode).firstChild()) or
  result = first(n.(ParExpr).getExpr()) or
  result = first(n.(SynchronizedStmt).getExpr()) or
  result = n and n instanceof Stmt and
    not n instanceof PostOrderNode and
    not n instanceof SynchronizedStmt
}

/**
 * Bind `last` to a node inside the body of `try` that may finish with `completion`
 * such that control will be transferred to a `catch` block or the `finally` block of `try`.
 *
 * In other words, `last` is either a resource declaration that throws, or a
 * node in the `try` block that may not complete normally, or a node in
 * the `try` block that has no control flow successors inside the block.
 */
private predicate catchOrFinallyCompletion(TryStmt try, ControlFlowNode last, int completion) {
  last(try.getBlock(), last, completion) or
  last(try.getAResourceDecl(), last, completion) and completion = throwCompletion(_)
}

/**
 * Bind `last` to a node inside the body of `try` that may finish with `completion`
 * such that control may be transferred to the `finally` block (if it exists).
 *
 * In other words, if `last` throws an exception it is possibly not caught by any
 * of the catch clauses.
 */
private predicate uncaught(TryStmt try, ControlFlowNode last, int completion) {
  catchOrFinallyCompletion(try, last, completion) and
  (
    exists (ThrowableType thrown |
      thrown = thrownInBody(try) and completion = throwCompletion(thrown) and
      not mustCatch(try.getACatchClause(), thrown)
    ) or
    completion = normalCompletion() or completion = returnCompletion() or
    completion = anonymousBreakCompletion() or completion = labelledBreakCompletion(_) or
    completion = anonymousContinueCompletion() or completion = labelledContinueCompletion(_)
  )
}

/**
 * Bind `last` to a node inside `try` that may finish with `completion` such
 * that control may be transferred to the `finally` block (if it exists).
 *
 * This is similar to `uncaught`, but also includes final statements of `catch`
 * clauses.
 */
private predicate finallyPred(TryStmt try, ControlFlowNode last, int completion) {
  uncaught(try, last, completion) or
  last(try.getACatchClause(), last, completion)
}

/**
 * Bind `last` to a cfg node nested inside `n` (or, indeed, `n` itself) such
 * that `last` may be the last node during an execution of `n` and finish
 * with the given completion.
 *
 * A `booleanCompletion` implies that `n` is an `Expr`. Any abnormal
 * completion besides `throwCompletion` implies that `n` is a `Stmt`.
 */
cached
private predicate last(ControlFlowNode n, ControlFlowNode last, int completion) {
  // Exceptions are propagated from any sub-expression.
  exists (Expr e | e.getParent() = n | last(e, last, completion) and completion = throwCompletion(_)) or

  // If an expression doesn't finish with a throw completion, then it executes normally with
  // either a `normalCompletion` or a `booleanCompletion`.

  // A boolean completion in a non-boolean context just indicates a normal completion
  // and a normal completion in a boolean context indicates an arbitrary boolean completion.
  last(n, last, normalCompletion()) and inBooleanContext(n) and completion = basicBooleanCompletion(_) or
  last(n, last, booleanCompletion(_, _)) and not inBooleanContext(n) and completion = normalCompletion() or

  // Logic expressions and conditional expressions are executed in AST pre-order to facilitate
  // proper short-circuit representation. All other expressions are executed in post-order.

  // The last node of a logic expression is either in the right operand with an arbitrary
  // completion, or in the left operand with the corresponding boolean completion.
  exists (AndLogicalExpr andexpr | andexpr = n |
    last(andexpr.getLeftOperand(), last, completion) and completion = booleanCompletion(false, _) or
    last(andexpr.getRightOperand(), last, completion)
  ) or
  exists (OrLogicalExpr orexpr | orexpr = n |
    last(orexpr.getLeftOperand(), last, completion) and completion = booleanCompletion(true, _) or
    last(orexpr.getRightOperand(), last, completion)
  ) or

  // The last node of a `LogNotExpr` is in its sub-expression with an inverted boolean completion
  // (or a `normalCompletion`).
  exists (int subcompletion | last(n.(LogNotExpr).getExpr(), last, subcompletion) |
    subcompletion = normalCompletion() and completion = normalCompletion() and not inBooleanContext(n) or
    exists (boolean outervalue, boolean innervalue |
      subcompletion = booleanCompletion(outervalue, innervalue) and
      completion = booleanCompletion(outervalue.booleanNot(), innervalue)
    )
  ) or

  // The last node of a `ConditionalExpr` is in either of its branches.
  exists (ConditionalExpr condexpr | condexpr = n |
    last(condexpr.getFalseExpr(), last, completion) or
    last(condexpr.getTrueExpr(), last, completion)
  ) or

  // Parentheses are skipped in the CFG.
  last(n.(ParExpr).getExpr(), last, completion) or

  // The last node of a node executed in post-order is the node itself.
  n.(PostOrderNode).mayCompleteNormally() and last = n and completion = normalCompletion() or

  last = n and completion = basicBooleanCompletion(n.(BooleanLiteral).getBooleanLiteral()) or

  // The last statement in a block is any statement that does not complete normally,
  // or the last statement.
  exists (Block blk | blk = n |
    last(blk.getAStmt(), last, completion) and completion != normalCompletion() or
    last(blk.getStmt(blk.getNumStmt()-1), last, completion)
  ) or

  // The last node in an `if` statement is the last node in either of its branches or
  // the last node of the condition with a false-completion in the absence of an else-branch.
  exists (IfStmt ifstmt | ifstmt = n |
    last(ifstmt.getCondition(), last, booleanCompletion(false, _)) and completion = normalCompletion() and not exists(ifstmt.getElse()) or
    last(ifstmt.getThen(), last, completion) or
    last(ifstmt.getElse(), last, completion)
  ) or

  // A loop may terminate normally if its condition is false...
  exists (LoopStmt loop | loop = n |
    last(loop.getCondition(), last, booleanCompletion(false, _)) and completion = normalCompletion() or
    // ...or if it's an enhanced for loop running out of items to iterate over...
    // ...which may happen either immediately after the loop expression...
    last(loop.(EnhancedForStmt).getExpr(), last, completion) and completion = normalCompletion() or
    exists (int bodyCompletion | last(loop.getBody(), last, bodyCompletion) |
      // ...or after the last node in the loop's body in an iteration that would otherwise continue.
      loop instanceof EnhancedForStmt and continues(bodyCompletion, loop) and completion = normalCompletion() or
      // Otherwise the last node is the last node in the loop's body...
      // ...if it is an unlabelled `break` (causing the entire loop to complete normally)
      (if bodyCompletion = anonymousBreakCompletion() then
        completion = normalCompletion()
      // ...or if it is some other completion that does not continue the loop.
      else
        (not continues(bodyCompletion, loop) and completion = bodyCompletion))
    )
  ) or

  // `try` statements are a bit more complicated:
  exists (TryStmt try | try = n |
    // the last node in a `try` is the last node in its `finally` block
    exists (int finallyCompletion | last(try.getFinally(), last, finallyCompletion) |
      // if the `finally` block completes normally, it resumes any completion that
      // was current before the `finally` block was entered
      if finallyCompletion = normalCompletion() then
        finallyPred(try, _, completion)
      else
        // otherwise, just take the completion of the `finally` block itself
        completion = finallyCompletion
    ) or

    // if there is no `finally` block, take the last node of the body or
    // any of the `catch` clauses
    not exists (try.getFinally()) and finallyPred(try, last, completion)
  ) or

  // handle `switch` statements
  exists (SwitchStmt switch | switch = n |
    // unlabelled `break` causes the whole `switch` to complete normally
    last(switch.getAStmt(), last, anonymousBreakCompletion()) and completion = normalCompletion() or
    // any other abnormal completion is propagated
    (last(switch.getAStmt(), last, completion) and
     completion != anonymousBreakCompletion() and completion != normalCompletion()) or
    // if the last case completes normally, then so does the switch
    last(switch.getStmt(strictcount(switch.getAStmt())-1), last, normalCompletion()) and completion = normalCompletion() or
    // if no default case exists, then normal completion of the expression may terminate the switch
    not exists(switch.getDefaultCase()) and last(switch.getExpr(), last, completion) and completion = normalCompletion()
  ) or

  // the last statement of a synchronized statement is the last statement of its body
  last(n.(SynchronizedStmt).getBlock(), last, completion) or

  // `return` statements give rise to a `Return` completion
  last = (ReturnStmt)n and completion = returnCompletion() or

  // `throw` statements or throwing calls give rise to ` Throw` completion
  exists (ThrowableType tt | mayThrow(n, tt) | last = n and completion = throwCompletion(tt)) or

  // `break` statements give rise to a `Break` completion
  exists (BreakStmt break | break = n and last = n |
    completion = labelledBreakCompletion(break.getLabel()) or
    not exists(break.getLabel()) and completion = anonymousBreakCompletion()
  ) or

  // `continue` statements give rise to a `Continue` completion
  exists (ContinueStmt cont | cont = n and last = n |
    completion = labelledContinueCompletion(cont.getLabel()) or
    not exists(cont.getLabel()) and completion = anonymousContinueCompletion()
  ) or

  // the last node in an `ExprStmt` is the last node in the expression
  last(n.(ExprStmt).getExpr(), last, completion) and completion = normalCompletion() or

  // the last statement of a labeled statement is the last statement of its body...
  exists (LabeledStmt lbl, int bodyCompletion | lbl = n and last(lbl.getStmt(), last, bodyCompletion) |
    // ...except if it's a `break` that refers to this labelled statement
    if bodyCompletion = labelledBreakCompletion(lbl.getLabel()) then
      completion = normalCompletion()
    else
      completion = bodyCompletion
  ) or

  // the last statement of a `catch` clause is the last statement of its block
  last(n.(CatchClause).getBlock(), last, completion) or

  // the last node in a variable declaration statement is in the last of its individual declarations
  exists (LocalVariableDeclStmt s | s = n |
    last(s.getVariable(count(s.getAVariable())), last, completion) and completion = normalCompletion()
  )
}

/**
 * Compute the intra-procedural successors of cfg node `n`, assuming its
 * execution finishes with the given completion.
 */
cached
private ControlFlowNode succ(ControlFlowNode n, int completion) {
  // Callables serve as their own exit nodes.
  exists (Callable c | last(c.getBody(), n, completion) | result = c) or

  // Logic expressions and conditional expressions execute in AST pre-order.
  completion = normalCompletion() and
  (result = first(n.(AndLogicalExpr).getLeftOperand()) or
  result = first(n.(OrLogicalExpr).getLeftOperand()) or
  result = first(n.(LogNotExpr).getExpr()) or
  result = first(n.(ConditionalExpr).getCondition())) or

  // If a logic expression doesn't short-circuit then control flows from its left operand to its right.
  exists (AndLogicalExpr e |
    last(e.getLeftOperand(), n, completion) and completion = booleanCompletion(true, _) and
    result = first(e.getRightOperand())
  ) or
  exists (OrLogicalExpr e |
    last(e.getLeftOperand(), n, completion) and completion = booleanCompletion(false, _) and
    result = first(e.getRightOperand())
  ) or

  // Control flows to the corresponding branch depending on the boolean completion of the condition.
  exists (ConditionalExpr e |
    last(e.getCondition(), n, completion) and completion = booleanCompletion(true, _) and result = first(e.getTrueExpr()) or
    last(e.getCondition(), n, completion) and completion = booleanCompletion(false, _) and result = first(e.getFalseExpr())
  ) or

  // In other expressions control flows from left to right and ends in the node itself.
  exists (PostOrderNode p, int i | last(p.getChildNode(i), n, completion) and completion = normalCompletion() |
    result = first(p.getChildNode(i+1)) or
    not exists(p.getChildNode(i+1)) and result = p
  ) or

  // Statements within a block execute sequentially.
  result = first(n.(Block).getStmt(0)) and completion = normalCompletion() or
  exists (Block blk, int i |
    last(blk.getStmt(i), n, completion) and completion = normalCompletion() and result = first(blk.getStmt(i+1))
  ) or

  // Control flows to the corresponding branch depending on the boolean completion of the condition.
  exists (IfStmt s |
    n = s and result = first(s.getCondition()) and completion = normalCompletion() or
    last(s.getCondition(), n, completion) and completion = booleanCompletion(true, _) and result = first(s.getThen()) or
    last(s.getCondition(), n, completion) and completion = booleanCompletion(false, _) and result = first(s.getElse())
  ) or

  // For statements:
  exists (ForStmt for, ControlFlowNode condentry |
    // Any part of the control flow that aims for the condition needs to hit either the condition...
    condentry = first(for.getCondition()) or
    // ...or the body if the for doesn't include a condition.
    not exists (for.getCondition()) and condentry = first(for.getStmt())
    |
    // From the entry point, which is the for statement itself, control goes to either the first init expression...
    n = for and result = first(for.getInit(0)) and completion = normalCompletion() or
    // ...or the condition if the for doesn't include init expressions.
    n = for and not exists(for.getAnInit()) and result = condentry and completion = normalCompletion() or
    // Init expressions execute sequentially, after which control is transferred to the condition.
    exists (int i | last(for.getInit(i), n, completion) and completion = normalCompletion() |
      result = first(for.getInit(i+1)) or
      not exists(for.getInit(i+1)) and result = condentry
    ) or
    // The true-successor of the condition is the body of the for loop.
    last(for.getCondition(), n, completion) and completion = booleanCompletion(true, _) and result = first(for.getStmt()) or
    // The updates execute sequentially, after which control is transferred to the condition.
    exists (int i | last(for.getUpdate(i), n, completion) and completion = normalCompletion() |
      result = first(for.getUpdate(i+1)) or
      not exists(for.getUpdate(i+1)) and result = condentry
    ) or
    // The back edge of the loop: control goes to either the first update or the condition if no updates exist.
    last(for.getStmt(), n, completion) and continues(completion, for) and
      (result = first(for.getUpdate(0)) or
      result = condentry and not exists(for.getAnUpdate()))
  ) or

  // Enhanced for statements:
  exists (EnhancedForStmt for |
    // First the expression gets evaluated...
    n = for and result = first(for.getExpr()) and completion = normalCompletion() or
    // ...then the variable gets assigned...
    last(for.getExpr(), n, completion) and completion = normalCompletion() and result = for.getVariable() or
    // ...and then control goes to the body of the loop.
    n = for.getVariable() and result = first(for.getStmt()) and completion = normalCompletion() or
    // Finally, the back edge of the loop goes to reassign the variable.
    last(for.getStmt(), n, completion) and continues(completion, for) and result = for.getVariable()
  ) or

  // While loops start at the condition...
  result = first(n.(WhileStmt).getCondition()) and completion = normalCompletion() or
  // ...and do-while loops start at the body.
  result = first(n.(DoStmt).getStmt()) and completion = normalCompletion() or
  exists (LoopStmt loop | loop instanceof WhileStmt or loop instanceof DoStmt |
    // Control goes from the condition via a true-completion to the body...
    last(loop.getCondition(), n, completion) and completion = booleanCompletion(true, _) and result = first(loop.getBody()) or
    // ...and through the back edge from the body back to the condition.
    last(loop.getBody(), n, completion) and continues(completion, loop) and result = first(loop.getCondition())
  ) or

  // Resource declarations in a try-with-resources execute sequentially.
  exists (TryStmt try, int i | last(try.getResourceDecl(i), n, completion) and completion = normalCompletion() |
    result = first(try.getResourceDecl(i+1)) or
    not exists(try.getResourceDecl(i+1)) and result = first(try.getBlock())
  ) or

  // After the last resource declaration, control transfers to the body.
  exists (TryStmt try | n = try and completion = normalCompletion() |
    result = first(try.getResourceDecl(0)) or
    not exists(try.getAResourceDecl()) and result = first(try.getBlock())
  ) or

  // exceptional control flow
  exists (TryStmt try | catchOrFinallyCompletion(try, n, completion) |
    // if the body of the `try` throws...
    exists (ThrowableType tt | completion = throwCompletion(tt) |
      // ...control transfers to a catch clause...
      result = first(handlingCatchClause(try, tt)) or
      // ...or to the finally block
      not mustCatch(try.getACatchClause(), tt) and result = first(try.getFinally())
    ) or

    // if the body completes normally, control transfers to the finally block
    not completion = throwCompletion(_) and result = first(try.getFinally())
  ) or

  // after each catch clause, control transfers to the finally block
  exists (TryStmt try | last(try.getACatchClause(), n, completion) |
    result = first(try.getFinally())
  ) or

  // Catch clauses first assign their variable and then execute their block
  exists (CatchClause cc | completion = normalCompletion() |
    n = cc and result = first(cc.getVariable()) or
    last(cc.getVariable(), n, completion) and result = first(cc.getBlock())
  ) or

  // Switch statements
  exists (SwitchStmt switch | completion = normalCompletion() |
    // From the entry point control is transferred first to the expression...
    n = switch and result = first(switch.getExpr()) or
    // ...and then to one of the cases.
    last(switch.getExpr(), n, completion) and result = first(switch.getACase()) or
    // Statements within a switch body execute sequentially.
    exists (int i | last(switch.getStmt(i), n, completion) and result = first(switch.getStmt(i+1)))
  ) or

  // No edges in a SwitchCase - the constant expression in a ConstCase isn't included in the CFG.

  // Synchronized statements execute their expression _before_ synchronization, so the CFG reflects that.
  exists (SynchronizedStmt synch | completion = normalCompletion() |
    last(synch.getExpr(), n, completion) and result = synch or
    n = synch and result = first(synch.getBlock())
  ) or

  result = first(n.(ExprStmt).getExpr()) and completion = normalCompletion() or

  result = first(n.(LabeledStmt).getStmt()) and completion = normalCompletion() or

  // Variable declarations in a variable declaration statement are executed sequentially.
  exists (LocalVariableDeclStmt s | completion = normalCompletion() |
    n = s and result = first(s.getVariable(1)) or
    exists (int i | last(s.getVariable(i), n, completion) and result = first(s.getVariable(i+1)))
  )
}

/** The intra-procedural successor of `n`. */
private ControlFlowNode succ(ControlFlowNode n) {
  result = succ(n, _)
}

/*
 * Conditions give rise to nodes with two normal successors, a true successor
 * and a false successor. At least one of them is completely contained in the
 * AST node of the branching construct and is therefore tagged with the
 * corresponding `booleanCompletion` in the `succ` relation (for example, the
 * then-branch of an if-statement, or the right operand of a binary logic
 * expression). The other successor may be tagged with either the corresponding
 * `booleanCompletion` (for example in an if-statement with an else-branch or
 * in a `ConditionalExpr`) or a `normalCompletion` (for example in an
 * if-statement without an else-part).
 * 
 * If the other successor ends a finally block it may also be tagged with an
 * abnormal completion instead of a `normalCompletion`. This completion is
 * calculated by the `resumption` predicate. In this case the successor might
 * no longer be unique, as there can be multiple completions to be resumed
 * after the finally block.
 */

/**
 * Get the _resumption_ for cfg node `n`, that is, the completion according
 * to which control flow is determined if `n` completes normally.
 *
 * In most cases, the resumption is simply the normal completion, except if
 * `n` is the last node of a `finally` block, in which case it is the
 * completion of any predecessors of the `finally` block as determined by
 * predicate `finallyPred`, since their completion is resumed after normal
 * completion of the `finally`.
 */
private int resumption(ControlFlowNode n) {
  exists (TryStmt try | lastInFinally(try, n) and finallyPred(try, _, result)) or
  not lastInFinally(_, n) and result = normalCompletion()
}

private predicate lastInFinally(TryStmt try, ControlFlowNode n) {
  last(try.getFinally(), n, normalCompletion())
}

/**
 * A true- or false-successor that is tagged with the corresponding `booleanCompletion`.
 *
 * That is, the `booleanCompletion` is the label of the edge in the CFG.
 */
private ControlFlowNode mainBranchSucc(ControlFlowNode n, boolean b) {
  result = succ(n, booleanCompletion(_, b))
}

/**
 * A true- or false-successor that is not tagged with a `booleanCompletion`.
 *
 * That is, the label of the edge in the CFG is a `normalCompletion` or
 * some other completion if `n` occurs as the last node in a finally block.
 *
 * In the latter case, when `n` occurs as the last node in a finally block, there might be
 * multiple different such successors.
 */
private ControlFlowNode otherBranchSucc(ControlFlowNode n, boolean b) {
  exists (ControlFlowNode main | main = mainBranchSucc(n, b.booleanNot()) |
    result = succ(n, resumption(n)) and
    not result = main and
    (b = true or b = false)
  )
}

/** A true- or false-successor of `n`. */
cached
private ControlFlowNode branchSuccessor(ControlFlowNode n, boolean branch) {
  result = mainBranchSucc(n, branch) or
  result = otherBranchSucc(n, branch)
}

/** A control-flow node that branches based on a condition. */
class ConditionNode extends ControlFlowNode {
  ConditionNode() {
    exists (branchSuccessor(this, _))
  }

  /** A true- or false-successor of the `ConditionNode`. */
  ControlFlowNode getABranchSuccessor(boolean branch) {
    result = branchSuccessor(this, branch)
  }

  /** A true-successor of the `ConditionNode`. */
  ControlFlowNode getATrueSuccessor() {
    result = getABranchSuccessor(true)
  }

  /** A false-successor of the `ConditionNode`. */
  ControlFlowNode getAFalseSuccessor() {
    result = getABranchSuccessor(false)
  }

  /** The condition of this `ConditionNode`. This is equal to the node itself. */
  Expr getCondition() {
    result = this
  }
}
