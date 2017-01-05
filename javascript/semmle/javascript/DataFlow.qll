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

import Expr

/**
 * An expression or function/class declaration, viewed as a node in a data flow graph.
 */
class DataFlowNode extends @ast_node {
  DataFlowNode() {
    this instanceof Expr or
    this instanceof FunctionDeclStmt or
    this instanceof ClassDefinition
  }

  /**
   * Return another flow node from which data may flow to this node in one local step.
   */
  DataFlowNode localFlowPred() {
    // to be overridden by subclasses
    none()
  }

  /**
   * Non-local data flow step through global or captured variable.
   */
  DataFlowNode nonLocalFlowPred() {
    // to be overridden by subclasses
    none()
  }

  /**
   * A single data flow step.
   */
  DataFlowNode flowPred() {
    result = localFlowPred() or result = nonLocalFlowPred()
  }

  /**
   * Get a source flow node (that is, a node without a `localFlowPred()`) from which data
   * may flow to this node in zero or more local steps (that is, not involving data flow
   * through global or captured variables)
   */
  private DataFlowNode getALocalSource() {
    if exists(localFlowPred()) then
      result = localFlowPred().getALocalSource()
    else
      result = this
  }

  /**
   * Return a source flow node (that is, a node without a `localFlowPred()`) from which data
   * may flow to this node in zero or more steps, including at most one non-local step.
   *
   * The analysis performed by this predicate is flow-sensitive for local variables, but
   * flow-insensitive and incomplete for global variables and local variables captured
   * in an inner scope; all assignments to such a variable are considered to flow into all uses.
   * The analysis is furthermore heap-insensitive (that is, data flow through properties is
   * not tracked), and does not track flow through function calls, except for IIFEs.
   */
  DataFlowNode getASource() {
    result = getALocalSource() or
    // flow through non-local variable
    result = getALocalSource().nonLocalFlowPred().getALocalSource()
  }

  /**
   * Is the flow information for this node incomplete?
   *
   * This predicate holds if there may be a source flow node from which data flows into
   * this node, but that node is not a result of `getASource()` due to analysis incompleteness.
   * The parameter `cause` is bound to a string describing the source of incompleteness.
   *
   * For example, since this analysis is intra-procedural, data flow from actual arguments
   * to formal parameters is not modelled. Hence, if `p` is an access to a parameter,
   * `p.getASource()` does _not_ return the corresponding argument, and
   * `p.isIncomplete("call")` holds.
   */
  predicate isIncomplete(DataFlowIncompleteness cause) {
    none()
  }

  string toString() { result = this.(ASTNode).toString() }

  /** Get the location of the AST node underlying this data flow node. */
  Location getLocation() { result = this.(ASTNode).getLocation() }
}

/**
 * Classification of flows that are not modelled, or only modelled incompletely, by
 * `DataFlowNode`.
 */
class DataFlowIncompleteness extends string {
  DataFlowIncompleteness() {
    this = "call" or   // lack of inter-procedural analysis
    this = "heap" or   // lack of heap modelling
    this = "import" or // lack of module import/export modelling
    this = "global" or // incomplete modelling of global object
    this = "yield" or  // lack of yield/async/await modelling
    this = "eval"      // lack of `eval` modelling
  }
}

/**
 * Is there an `eval` that might affect the value of `lv`?
 */
private predicate maybeAffectedByEval(LocalVariable lv) {
  exists (CallExpr directEval |
    // only direct `eval`s can affect the enclosing scope
    directEval.getCallee().(GlobalVarAccess).getName() = "eval" |
    directEval.getParent+() = lv.getScope().getScopeElement()
  )
}

/**
 * Flow through variable accesses
 */
library class VarAccessFlow extends DataFlowNode, @varaccess {
  DataFlowNode localFlowPred() {
    // flow through local variable
    exists (VarDef def | localDefinitionReaches(_, def, this) | result = defSource(def)) or

    // flow through IIFE
    exists (ImmediatelyInvokedFunctionExpr iife, SimpleParameter parm |
      isIIFEParameterAccess(iife, parm) and
      iife.argumentPassing(parm, (Expr)result)
    )
  }

  /** Is this an access to parameter `parm` of immediately invoked function expression `iife`? */
  private predicate isIIFEParameterAccess(ImmediatelyInvokedFunctionExpr iife, SimpleParameter parm) {
    this = parm.getVariable().getAnAccess() and
    parm = iife.getAParameter()
  }

  DataFlowNode nonLocalFlowPred() {
    exists (Variable v, VarDef def | v.isGlobal() or v.isCaptured() |
      v = def.getAVariable() and
      result = defSource(def) and
      this = v.getAnAccess()
    )
  }

  private DataFlowNode defSource(VarDef def) {
    def = this.(VarUse).getADef() and
    (result = def.getSource() or
     result = (CompoundAssignExpr)def or
     result = (UpdateExpr)def or
     result.(FunctionDeclStmt).getId() = def or
     result.(ClassDefinition).getIdentifier() = def)
  }

  predicate isIncomplete(DataFlowIncompleteness cause) {
    exists (VarDef def | def = this.(VarUse).getADef() |
      def instanceof Parameter and cause = "call" or
      def instanceof ImportSpecifier and cause = "import" or
      exists (EnhancedForLoop efl | def = efl.getIteratorExpr()) and cause = "heap" or
      exists (ComprehensionBlock cb | def = cb.getIterator()) and cause = "yield" or
      def.getTarget() instanceof DestructuringPattern and cause = "heap"
    ) or
    exists (Variable v | this = v.getAnAccess() |
      v.isGlobal() and cause = "global" or
      v instanceof ArgumentsObject and cause = "call" or
      maybeAffectedByEval(v) and cause = "eval"
    )
  }
}

/** Flow through parentheses. */
library class ParExprFlow extends DataFlowNode, @parexpr {
  DataFlowNode localFlowPred() {
    result = this.(ParExpr).getExpression()
  }
}

/** Flow through comma expressions. */
library class SeqExprFlow extends DataFlowNode, @seqexpr {
  DataFlowNode localFlowPred() {
    result = this.(SeqExpr).getLastOperand()
  }
}

/** Flow through short circuit expressions. */
library class LogicalBinaryExprFlow extends DataFlowNode, @binaryexpr {
  LogicalBinaryExprFlow() { this instanceof LogicalBinaryExpr }

  DataFlowNode localFlowPred() {
    result = this.(LogicalBinaryExpr).getAnOperand()
  }
}

/** Flow through assignments. */
library class AssignExprFlow extends DataFlowNode, @assignexpr {
  DataFlowNode localFlowPred() {
    result = this.(AssignExpr).getRhs()
  }
}

/** Flow through conditional expressions. */
library class ConditionalExprFlow extends DataFlowNode, @conditionalexpr {
  DataFlowNode localFlowPred() {
    result = this.(ConditionalExpr).getABranch()
  }
}

library class InvokeExprFlow extends DataFlowNode, @invokeexpr {
  // inter-procedural flow is not modelled; mark as incomplete
  predicate isIncomplete(DataFlowIncompleteness cause) { cause = "call" }
}

library class PropAccessFlow extends DataFlowNode, @propaccess {
  // flow through the heap is not modelled; mark as incomplete
  predicate isIncomplete(DataFlowIncompleteness cause) { cause = "heap" }
}

library class ThisFlow extends DataFlowNode, @thisexpr {
  // inter-procedural flow is not modelled; mark as incomplete
  predicate isIncomplete(DataFlowIncompleteness cause) { cause = "call" }
}

library class SuperFlow extends DataFlowNode, @superexpr {
  // inter-procedural flow is not modelled; mark as incomplete
  predicate isIncomplete(DataFlowIncompleteness cause) { cause = "call" }
}

library class NewTargetFlow extends DataFlowNode, @newtargetexpr {
  // inter-procedural flow is not modelled; mark as incomplete
  predicate isIncomplete(DataFlowIncompleteness cause) { cause = "call" }
}

library class YieldFlow extends DataFlowNode, @yieldexpr {
  // asynchronous flow is not modelled; mark as incomplete
  predicate isIncomplete(DataFlowIncompleteness cause) { cause = "yield" }
}

library class AwaitFlow extends DataFlowNode, @awaitexpr {
  // asynchronous flow is not modelled; mark as incomplete
  predicate isIncomplete(DataFlowIncompleteness cause) { cause = "yield" }
}

library class FunctionSentFlow extends DataFlowNode, @functionsentexpr {
  // asynchronous flow is not modelled; mark as incomplete
  predicate isIncomplete(DataFlowIncompleteness cause) { cause = "yield" }
}

/**
 * A data flow node that writes to an object property.
 */
abstract class PropWriteNode extends DataFlowNode {
  /**
   * The data flow node corresponding to the base object
   * whose property is written to.
   */
  abstract DataFlowNode getBase();

  /**
   * The name of the property being written,
   * if it can be statically determined.
   *
   * This predicate is undefined for dynamic property writes
   * such as `e[computePropertyName()] = rhs` and for spread
   * properties.
   */
  abstract string getPropertyName();

  /**
   * The data flow node corresponding to the value being written,
   * if it can be statically determined.
   *
   * This predicate is undefined for spread properties.
   */
  abstract DataFlowNode getRhs();
}

/**
 * A property assignment, viewed as a data flow node.
 */
class PropAssignNode extends PropWriteNode, @propaccess {
  PropAssignNode() {
    exists (Assignment assgn | assgn.getTarget() = this)
  }

  DataFlowNode getBase() { result = this.(PropAccess).getBase() }
  string getPropertyName() { result = this.(PropAccess).getPropertyName() }
  DataFlowNode getRhs() {
    exists (Assignment assgn | assgn.getTarget() = this | result = assgn.getRhs())
  }
}

/**
 * A property of an object literal, viewed as a data flow node that writes
 * to the corresponding property.
 */
class PropInitNode extends PropWriteNode, @expr {
  PropInitNode() { exists (ValueProperty vp | this = vp.getNameExpr()) }
  private ValueProperty getProperty() { this = result.getNameExpr() }
  DataFlowNode getBase() { result = getProperty().getObjectExpr() }
  string getPropertyName() { result = getProperty().getName() }
  DataFlowNode getRhs() { result = getProperty().getInit() }
}

/**
 * A call to `Object.defineProperty`, viewed as a data flow node that
 * writes to the corresponding property.
 */
class ObjectDefinePropNode extends PropWriteNode {
  ObjectDefinePropNode() { this instanceof CallToObjectDefineProperty }

  DataFlowNode getBase() { result = this.(CallToObjectDefineProperty).getBaseObject() }
  string getPropertyName() { result = this.(CallToObjectDefineProperty).getPropertyName() }
  DataFlowNode getRhs() {
    exists (ObjectExpr propdesc |
      propdesc = this.(CallToObjectDefineProperty).getPropertyDescriptor() and
      result = propdesc.getPropertyByName("value").getInit()
    )
  }
}

/**
 * A static member definition, viewed as a data flow node that adds
 * a property to the class.
 */
library class StaticMemberAsWrite extends PropWriteNode {
  StaticMemberAsWrite() {
    exists (MemberDefinition md | md.isStatic() and this = md.getNameExpr())
  }
  private MemberDefinition getMember() { this = result.getNameExpr() }
  DataFlowNode getBase() { result = getMember().getDeclaringClass().getDefinition() }
  string getPropertyName() { result = getMember().getName() }
  DataFlowNode getRhs() { result = getMember().getChildExpr(1) }
}

/**
 * A spread property of an object literal, viewed as a data flow node that writes
 * properties of the object literal.
 */
library class SpreadPropertyAsWrite extends PropWriteNode {
  SpreadPropertyAsWrite() { exists (SpreadProperty prop | this = prop.getInit()) }
  DataFlowNode getBase() { result.(ObjectExpr).getAProperty().getInit() = this }
  string getPropertyName() { none() }
  DataFlowNode getRhs() { none() }
}