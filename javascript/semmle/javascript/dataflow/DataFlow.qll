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
 * Provides classes for working with a data flow graph-based
 * program representation.
 *
 * We currently consider three kinds of data flow:
 *
 *   1. Flow within an expression, for example from the operands of a `&&`
 *      expression to the expression itself.
 *   2. Flow through local variables, that is, from definitions to uses.
 *      Captured variables are treated flow-insensitively, that is, all
 *      definitions are considered to flow to all uses, while for non-captured
 *      variables only definitions that can actually reach a use are considered.
 *   3. Flow into and out of immediately invoked function expressions, that is,
 *      flow from arguments to parameters, and from returned expressions to the
 *      function expression itself.
 *
 * Flow through global variables, object properties or function calls is not
 * modeled (except for immediately invoked functions as explained above).
 */

import javascript

module DataFlow {
  private newtype TNode =
     TValueNode(@dataflownode nd)
  or TSsaDefNode(SsaDefinition d)

  /**
   * A node in the data flow graph.
   */
  class Node extends TNode {
    /**
     * Gets a data flow node from which data may flow to this node in one local step.
     */
    Node getAPredecessor() {
      localFlowStep(result, this)
    }

    /**
     * Gets a data flow node to which data may flow from this node in one local step.
     */
    Node getASuccessor() {
      localFlowStep(this, result)
    }

    /**
     * DEPRECATED: This predicate is not scalable enough for use in production queries.
     *
     * Gets a source flow node (that is, a node without a predecessor in the data flow
     * graph) from which data may flow to this node in zero or more local steps.
     */
    deprecated Node getALocalSource() {
      not exists(getAPredecessor()) and result = this
      or
      result = getAPredecessor().getALocalSource()
    }

    /**
     * Holds if the flow information for this node is incomplete.
     *
     * This predicate holds if there may be a source flow node from which data flows into
     * this node, but that node is not a result of `getALocalSource()` due to analysis
     * incompleteness. The parameter `cause` is bound to a string describing the source of
     * incompleteness.
     *
     * For example, since this analysis is intra-procedural, data flow from actual arguments
     * to formal parameters is not modeled. Hence, if `p` is an access to a parameter,
     * `p.getALocalSource()` does _not_ return the corresponding argument, and
     * `p.isIncomplete("call")` holds.
     */
    predicate isIncomplete(Incompleteness cause) {
      isIncomplete(this, cause)
    }

    /** Gets type inference results for this data flow node. */
    AnalyzedNode analyze() {
      result = this
    }

    /** Gets the expression corresponding to this data flow node, if any. */
    Expr asExpr() { none() }

    /** Gets the basic block to which this node belongs. */
    BasicBlock getBasicBlock() { none() }

    /** Gets the container in which this node occurs. */
    StmtContainer getContainer() { result = getBasicBlock().getContainer() }

    /**
     * Holds if this element is at the specified location.
     * The location spans column `startcolumn` of line `startline` to
     * column `endcolumn` of line `endline` in file `filepath`.
     * For more information, see
     * [LGTM locations](https://lgtm.com/docs/ql/locations).
     */
    predicate hasLocationInfo(string filepath, int startline, int startcolumn,
                              int endline, int endcolumn) {
      filepath = "" and
      startline = 0 and startcolumn = 0 and
      endline = 0 and endcolumn = 0
    }

    /** Gets the file this data flow node comes from. */
    File getFile() {
      hasLocationInfo(result.getAbsolutePath(), _, _, _, _)
    }

    /** Gets a textual representation of this element. */
    string toString() { none() }
  }

  /**
   * An expression, property, or a function/class/namespace/enum declaration, viewed as a node in a data flow graph.
   */
  class ValueNode extends Node, TValueNode {

    ASTNode astNode;

    ValueNode() {
      this = TValueNode(astNode) and
      astNode instanceof DataFlowNode
    }

    /** Gets the expression or declaration this node corresponds to. */
    ASTNode getAstNode() {
      result = astNode
    }

    override Expr asExpr() {
      result = astNode
    }

    override BasicBlock getBasicBlock() {
      astNode = result.getANode()
    }

    override predicate hasLocationInfo(string filepath, int startline, int startcolumn,
                                       int endline, int endcolumn) {
      astNode.getLocation().hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
    }

    override string toString() {
      result = astNode.toString()
    }
  }

  /**
   * A node in the data flow graph which corresponds to an SSA variable definition.
   */
  class SsaDefinitionNode extends Node, TSsaDefNode {
    SsaDefinition ssa;

    SsaDefinitionNode() { this = TSsaDefNode(ssa) }

    /** Gets the SSA variable defined at this data flow node. */
    SsaVariable getSsaVariable() {
      result = ssa.getVariable()
    }

    override BasicBlock getBasicBlock() {
      result = ssa.getBasicBlock()
    }

    override predicate hasLocationInfo(string filepath, int startline, int startcolumn,
                                       int endline, int endcolumn) {
      ssa.hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
    }

    override string toString() {
      result = ssa.toString()
    }
  }

  /**
   * Gets the data flow node corresponding to `nd`.
   *
   * This predicate is only defined for expressions, properties, and for statements that declare
   * a function, a class, or a TypeScript namespace or enum.
   */
  ValueNode valueNode(ASTNode nd) { result.getAstNode() = nd }

  /** Gets the data flow node corresponding to `ssa`. */
  SsaDefinitionNode ssaDefinitionNode(SsaDefinition ssa) {
    result = TSsaDefNode(ssa)
  }

  /** Gets the node corresponding to the initialization of parameter `p`. */
  SsaDefinitionNode parameterNode(SimpleParameter p) {
    exists (SsaExplicitDefinition ssa | ssa.getDef() = p |
      result = ssaDefinitionNode(ssa)
    )
  }

  /**
   * A classification of flows that are not modeled, or only modeled incompletely, by
   * `DataFlowNode`:
   *
   * - `"await"`: missing flow through promises;
   * - `"call"`: missing inter-procedural data flow;
   * - `"eval"`: missing reflective data flow;
   * - `"global"`: missing ata flow through global variables;
   * - `"heap"`: missing data flow through properties;
   * - `"import"`: missing data flow through module imports;
   * - `"namespace"`: missing data flow through exported namespace members;
   * - `"yield"`: missing data flow through generators.
   */
  class Incompleteness extends string {
    Incompleteness() {
      this = "await" or
      this = "call" or
      this = "eval" or
      this = "global" or
      this = "heap" or
      this = "import" or
      this = "namespace" or
      this = "yield"
    }
  }

  /**
   * Holds if `call` may call `callee`, and this call should be
   * tracked by local data flow.
   */
  private predicate localCall(InvokeExpr call, Function callee) {
    call = callee.(ImmediatelyInvokedFunctionExpr).getInvocation()
  }

  /**
   * Holds if some call passes `arg` as the value of `parm, and this
   * call should be tracked by local data flow.
   */
  private predicate localArgumentPassing(Expr arg, Parameter parm) {
    any(ImmediatelyInvokedFunctionExpr iife).argumentPassing(parm, arg)
  }

  /**
   * Holds if data can flow from `node1` to `node2` in one local step.
   */
  cached
  predicate localFlowStep(Node pred, Node succ) {
    // flow into local variables
    exists (SsaDefinition ssa | succ = TSsaDefNode(ssa) |
      // from the rhs of an explicit definition into the variable
      pred = defSourceNode(ssa.(SsaExplicitDefinition).getDef())
      or
      // from any explicit definition or implicit init of a captured variable into
      // the capturing definition
      exists (SsaSourceVariable v, SsaDefinition predDef |
        v = ssa.(SsaVariableCapture).getSourceVariable() and
        predDef.getSourceVariable() = v and
        pred = TSsaDefNode(predDef) |
        predDef instanceof SsaExplicitDefinition or
        predDef instanceof SsaImplicitInit
      )
      or
      // from the inputs of phi and pi nodes into the node itself
      pred = TSsaDefNode(ssa.(SsaPseudoDefinition).getAnInput().getDefinition())
    )
    or
    // flow out of local variables
    exists (SsaVariable v |
      pred = TSsaDefNode(v.getDefinition()) and
      succ = valueNode(v.getAUse())
    )
    or
    exists (Expr predExpr, Expr succExpr |
      pred = valueNode(predExpr) and succ = valueNode(succExpr) |
      predExpr = succExpr.(ParExpr).getExpression()
      or
      predExpr = succExpr.(SeqExpr).getLastOperand()
      or
      predExpr = succExpr.(LogicalBinaryExpr).getAnOperand()
      or
      predExpr = succExpr.(AssignExpr).getRhs()
      or
      predExpr = succExpr.(ConditionalExpr).getABranch()
      or
      predExpr = succExpr.(TypeAssertion).getExpression()
      or
      predExpr = succExpr.(NonNullAssertion).getExpression()
      or
      predExpr = succExpr.(ExpressionWithTypeArguments).getExpression()
      or
      exists (Function f |
        predExpr = f.getAReturnedExpr() and
        localCall(succExpr, f)
      )
    )
  }

  /**
   * Gets the data flow node representing the source of variable definition `def`,
   * if any.
   */
  private Node defSourceNode(VarDef def) {
    // follow one step of the def-use chain, but only for definitions where
    // the lhs is a simple variable reference (as opposed to a destructuring
    // pattern)
    result = TValueNode(def.getSource()) and
    def.getTarget() instanceof VarRef
    or
    localArgumentPassing(result.asExpr(), def)
  }

  /**
   * Holds if the flow information for this node is incomplete.
   *
   * This predicate holds if there may be a source flow node from which data flows into
   * this node, but that node is not a result of `getALocalSource()` due to analysis incompleteness.
   * The parameter `cause` is bound to a string describing the source of incompleteness.
   *
   * For example, since this analysis is intra-procedural, data flow from actual arguments
   * to formal parameters is not modeled. Hence, if `p` is an access to a parameter,
   * `p.getALocalSource()` does _not_ return the corresponding argument, and
   * `p.isIncomplete("call")` holds.
   */
  predicate isIncomplete(Node nd, Incompleteness cause) {
    exists (SsaVariable ssa | nd = TSsaDefNode(ssa.getDefinition()) |
      defIsIncomplete(ssa.(SsaExplicitDefinition).getDef(), cause)
      or
      exists (Variable v | v = ssa.getSourceVariable() |
        v.isNamespaceExport() and cause = "namespace" or
        any(DirectEval e).mayAffect(v) and cause = "eval"
      )
    )
    or
    exists (GlobalVarAccess va |
      nd = valueNode((VarUse)va) and
      cause = "global"
    )
    or
    exists (Expr e | e = nd.asExpr() and cause = "call" |
      e instanceof InvokeExpr and
      not localCall(e, _)
      or
      e instanceof ThisExpr or e instanceof SuperExpr
      or
      e instanceof NewTargetExpr
      or
      e instanceof FunctionBindExpr
      or
      e instanceof TaggedTemplateExpr
    )
    or
    nd.asExpr() instanceof ExternalModuleReference and
    cause = "import"
    or
    nd.asExpr() instanceof PropAccess and
    cause = "heap"
    or
    exists (Expr e | e = nd.asExpr() |
      (e instanceof YieldExpr or e instanceof FunctionSentExpr) and
      cause = "yield"
      or
      (e instanceof AwaitExpr or e instanceof DynamicImportExpr) and
      cause = "await"
    )
  }

  /**
   * Holds if definition `def` cannot be completely analyzed due to `cause`.
   */
  private predicate defIsIncomplete(VarDef def, Incompleteness cause) {
    def instanceof Parameter and
    not localArgumentPassing(_, def) and
    cause = "call"
    or
    def instanceof ImportSpecifier and
    cause = "import"
    or
    exists (EnhancedForLoop efl | def = efl.getIteratorExpr()) and
    cause = "heap"
    or
    exists (ComprehensionBlock cb | def = cb.getIterator()) and
    cause = "yield"
    or
    def.getTarget() instanceof DestructuringPattern and
    cause = "heap"
  }

  import TypeInference
  import Configuration
  import TrackedNodes
}

/**
 * DEPRECATED: Use `DataFlow::Configuration` instead.
 */
deprecated class FlowTrackingConfiguration = DataFlow::Configuration;

/**
 * DEPRECATED: Use `AnalyzedDataFlowNode` instead.
 */
deprecated class AnalyzedFlowNode = DataFlow::AnalyzedNode;
