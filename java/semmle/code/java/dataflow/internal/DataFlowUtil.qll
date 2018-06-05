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
 * Basic definitions for use in the data flow library.
 */
private import java
private import semmle.code.java.dataflow.SSA
import semmle.code.java.dataflow.InstanceAccess

  cached
  private newtype TNode =
    TExprNode(Expr e) or
    TExplicitParameterNode(Parameter p) { exists(p.getCallable().getBody()) } or
    TImplicitVarargsArray(Call c) { c.getCallee().isVarargs() and not exists(Argument arg | arg.getCall() = c and arg.isExplicitVarargsArray()) } or
    TInstanceParameterNode(Callable c) { exists(c.getBody()) and not c.isStatic() } or
    TImplicitInstanceAccess(InstanceAccessExt ia) { not ia.isExplicit(_) }

  /**
   * An element, viewed as a node in a data flow graph. Either an expression,
   * a parameter, or an implicit varargs array creation.
   */
  class Node extends TNode {
    /** Gets a textual representation of this element. */
    string toString() { none() }

    /** The source location for this element. */
    Location getLocation() { none() }

    /** Gets the expression corresponding to this node, if any. */
    Expr asExpr() { result = this.(ExprNode).getExpr() }

    /** Gets the parameter corresponding to this node, if any. */
    Parameter asParameter() { result = this.(ExplicitParameterNode).getParameter() }

    /** Gets the type of this node. */
    Type getType() {
      result = this.asExpr().getType() or
      result = this.asParameter().getType() or
      exists(Parameter p | result = p.getType() and p.isVarargs() and p = this.(ImplicitVarargsArray).getCall().getCallee().getAParameter()) or
      result = this.(InstanceParameterNode).getCallable().getDeclaringType() or
      result = this.(ImplicitInstanceAccess).getInstanceAccess().getType()
    }

    /** Gets the callable in which this node occurs. */
    Callable getEnclosingCallable() {
      result = this.asExpr().getEnclosingCallable() or
      result = this.asParameter().getCallable() or
      result = this.(ImplicitVarargsArray).getCall().getEnclosingCallable() or
      result = this.(InstanceParameterNode).getCallable() or
      result = this.(ImplicitInstanceAccess).getInstanceAccess().getEnclosingCallable()
    }
  }

  /**
   * An expression, viewed as a node in a data flow graph.
   */
  class ExprNode extends Node, TExprNode {
    Expr expr;
    ExprNode() { this = TExprNode(expr) }
    override string toString() { result = expr.toString() }
    override Location getLocation() { result = expr.getLocation() }
    /** Gets the expression corresponding to this node. */
    Expr getExpr() { result = expr }
  }

  /** Gets the node corresponding to `e`. */
  ExprNode exprNode(Expr e) { result.getExpr() = e }

  /** An explicit or implicit parameter. */
  abstract class ParameterNode extends Node {
    /**
     * Holds if this node is the parameter of `c` at the specified (zero-based)
     * position. The implicit `this` parameter is considered to have index `-1`.
     */
    abstract predicate isParameterOf(Callable c, int pos);
  }

  /**
   * A parameter, viewed as a node in a data flow graph.
   */
  class ExplicitParameterNode extends ParameterNode, TExplicitParameterNode {
    Parameter param;
    ExplicitParameterNode() { this = TExplicitParameterNode(param) }
    override string toString() { result = param.toString() }
    override Location getLocation() { result = param.getLocation() }
    /** Gets the parameter corresponding to this node. */
    Parameter getParameter() { result = param }
    override predicate isParameterOf(Callable c, int pos) {
      c.getParameter(pos) = param
    }
  }

  /** Gets the node corresponding to `p`. */
  ExplicitParameterNode parameterNode(Parameter p) { result.getParameter() = p }

  /**
   * An implicit varargs array creation expression.
   *
   * A call `f(x1, x2)` to a method `f(A... xs)` desugars to `f(new A[]{x1, x2})`,
   * and this node corresponds to such an implicit array creation.
   */
  class ImplicitVarargsArray extends Node, TImplicitVarargsArray {
    Call call;
    ImplicitVarargsArray() { this = TImplicitVarargsArray(call) }
    override string toString() { result = "new ..[] { .. }" }
    override Location getLocation() { result = call.getLocation() }
    /** Gets the call containing this varargs array creation argument. */
    Call getCall() { result = call }
  }

  /**
   * An instance parameter for an instance method or constructor.
   */
  class InstanceParameterNode extends ParameterNode, TInstanceParameterNode {
    Callable callable;
    InstanceParameterNode() { this = TInstanceParameterNode(callable) }
    override string toString() { result = "parameter this" }
    override Location getLocation() { result = callable.getLocation() }
    /** Gets the callable containing this `this` parameter. */
    Callable getCallable() { result = callable }
    override predicate isParameterOf(Callable c, int pos) {
      callable = c and pos = -1
    }
  }

  /**
   * An implicit read of `this` or `A.this`.
   */
  class ImplicitInstanceAccess extends Node, TImplicitInstanceAccess {
    InstanceAccessExt ia;
    ImplicitInstanceAccess() { this = TImplicitInstanceAccess(ia) }
    override string toString() { result = ia.toString() }
    override Location getLocation() { result = ia.getLocation() }
    InstanceAccessExt getInstanceAccess() { result = ia }
  }

  /** Holds if `n` is an access to an unqualified `this` at `cfgnode`. */
  private predicate thisAccess(Node n, ControlFlowNode cfgnode) {
    n.(InstanceParameterNode).getCallable().getBody() = cfgnode or
    exists(InstanceAccess ia | ia = n.asExpr() and ia = cfgnode and ia.isOwnInstanceAccess()) or
    n.(ImplicitInstanceAccess).getInstanceAccess().(OwnInstanceAccess).getCfgNode() = cfgnode
  }

  /** Calculation of the relative order in which `this` references are read. */
  private module ThisFlow {
    private predicate thisAccess(Node n, BasicBlock b, int i) {
      thisAccess(n, b.getNode(i))
    }

    private predicate thisRank(Node n, BasicBlock b, int rankix) {
      exists(int i |
        i = rank[rankix](int j | thisAccess(_, b, j)) and
        thisAccess(n, b, i)
      )
    }

    private int lastRank(BasicBlock b) {
      result = max(int rankix | thisRank(_, b, rankix))
    }

    private predicate blockPrecedesThisAccess(BasicBlock b) {
      thisAccess(_, b.getABBSuccessor*(), _)
    }

    private predicate thisAccessBlockReaches(BasicBlock b1, BasicBlock b2) {
      thisAccess(_, b1, _) and b2 = b1.getABBSuccessor() or
      exists(BasicBlock mid |
        thisAccessBlockReaches(b1, mid) and
        b2 = mid.getABBSuccessor() and
        not thisAccess(_, mid, _) and
        blockPrecedesThisAccess(b2)
      )
    }

    private predicate thisAccessBlockStep(BasicBlock b1, BasicBlock b2) {
      thisAccessBlockReaches(b1, b2) and
      thisAccess(_, b2, _)
    }

    /** Holds if `n1` and `n2` are control-flow adjacent references to `this`. */
    predicate adjacentThisRefs(Node n1, Node n2) {
      exists(int rankix, BasicBlock b |
        thisRank(n1, b, rankix) and
        thisRank(n2, b, rankix+1)
      ) or
      exists(BasicBlock b1, BasicBlock b2 |
        thisRank(n1, b1, lastRank(b1)) and
        thisAccessBlockStep(b1, b2) and
        thisRank(n2, b2, 1)
      )
    }
  }

  /**
   * Holds if data can flow from `node1` to `node2` in zero or more
   * local (intra-procedural) steps.
   */
  predicate localFlow(Node node1, Node node2) {
    localFlowStep*(node1, node2)
  }

  /**
   * Holds if the `FieldRead` is not completely determined by explicit SSA
   * updates.
   */
  predicate hasNonlocalValue(FieldRead fr) {
    not exists(SsaVariable v | v.getAUse() = fr) or
    exists(SsaVariable v, SsaVariable def |
      v.getAUse() = fr and def = v.getAnUltimateDefinition()
      |
      def instanceof SsaImplicitInit or
      def instanceof SsaImplicitUpdate
    )
  }

  /**
   * Holds if data can flow from `node1` to `node2` in one local step.
   */
  cached
  predicate localFlowStep(Node node1, Node node2) {
    // Variable flow steps through adjacent def-use and use-use pairs.
    exists(SsaExplicitUpdate upd |
      upd.getDefiningExpr().(VariableAssign).getSource() = node1.asExpr() or
      upd.getDefiningExpr().(AssignOp) = node1.asExpr()
      |
      node2.asExpr() = upd.getAFirstUse()
    ) or
    exists(SsaImplicitInit init |
      init.isParameterDefinition(node1.asParameter()) and
      node2.asExpr() = init.getAFirstUse()
    ) or
    adjacentUseUse(node1.asExpr(), node2.asExpr()) and
    not exists(FieldRead fr | hasNonlocalValue(fr) and fr.getField().isStatic() and fr = node1.asExpr())
    or
    ThisFlow::adjacentThisRefs(node1, node2) or
    node2.asExpr().(ParExpr).getExpr() = node1.asExpr() or
    node2.asExpr().(CastExpr).getExpr() = node1.asExpr() or
    node2.asExpr().(ConditionalExpr).getTrueExpr() = node1.asExpr() or
    node2.asExpr().(ConditionalExpr).getFalseExpr() = node1.asExpr() or
    node2.asExpr().(AssignExpr).getSource() = node1.asExpr()
  }

  /**
   * Gets the node that occurs as the qualifier of `fa`.
   */
  Node getFieldQualifier(FieldAccess fa) {
    fa.getField() instanceof InstanceField and
    (
      result.asExpr() = fa.getQualifier() or
      result.(ImplicitInstanceAccess).getInstanceAccess().isImplicitFieldQualifier(fa)
    )
  }

  /** Gets the instance argument of a non-static call. */
  Node getInstanceArgument(Call call) {
    call instanceof ClassInstanceExpr and result.asExpr() = call or
    call instanceof MethodAccess and result.asExpr() = call.getQualifier() and not call.getCallee().isStatic() or
    result.(ImplicitInstanceAccess).getInstanceAccess().isImplicitMethodQualifier(call) or
    result.(ImplicitInstanceAccess).getInstanceAccess().isImplicitThisConstructorArgument(call)
  }


