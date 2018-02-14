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

import java
private import DataFlowUtil
private import semmle.code.java.dataflow.SSA

  /**
   * A data flow node that occurs as the argument of a call and is passed as-is
   * to the callable. Arguments that are wrapped in an implicit varargs array
   * creation are not included, but the implicitly created array is.
   * Instance arguments are also included.
   */
  class ArgumentNode extends Node {
    ArgumentNode() {
      exists(Argument arg | this.asExpr() = arg | not arg.isVararg()) or
      this instanceof ImplicitVarargsArray or
      this = getInstanceArgument(_)
    }

    /**
     * Holds if this argument occurs at the given position in the given call.
     * The instance argument is considered to have index `-1`.
     */
    predicate argumentOf(Call call, int pos) {
      exists(Argument arg | this.asExpr() = arg | call = arg.getCall() and pos = arg.getPosition()) or
      call = this.(ImplicitVarargsArray).getCall() and pos = call.getCallee().getNumberOfParameters() - 1 or
      pos = -1 and this = getInstanceArgument(call)
    }
  }

  /** A data flow node that occurs as the result of a `ReturnStmt`. */
  class ReturnNode extends ExprNode {
    ReturnNode() {
      exists(ReturnStmt ret | this.getExpr() = ret.getResult())
    }
  }

  /**
   * Holds if the `FieldRead` is not completely determined by explicit SSA
   * updates.
   */
  private predicate hasNonlocalValue(FieldRead fr) {
    not exists(SsaVariable v | v.getAUse() = fr) or
    exists(SsaVariable v, SsaVariable def |
      v.getAUse() = fr and def = v.getAnUltimateDefinition()
      |
      def instanceof SsaImplicitInit or
      def instanceof SsaImplicitUpdate
    )
  }

  /**
   * Holds if data can flow from `node1` to `node2` through a static field.
   */
  private predicate staticFieldStep(ExprNode node1, ExprNode node2) {
    exists(Field f, FieldRead fr |
      f.isStatic() and
      f.getAnAssignedValue() = node1.getExpr() and
      fr.getField() = f and
      fr = node2.getExpr() and
      hasNonlocalValue(fr)
    )
  }

  /**
   * Holds if data can flow from `node1` to `node2` through variable capture.
   */
  private predicate variableCaptureStep(Node node1, ExprNode node2) {
    exists(SsaImplicitInit closure, SsaVariable captured |
      closure.captures(captured) and
      node2.getExpr() = closure.getAFirstUse()
      |
      node1.asExpr() = captured.getAUse() or
      not exists(captured.getAUse()) and
      exists(SsaVariable capturedDef | capturedDef = captured.getAnUltimateDefinition() |
        capturedDef.(SsaImplicitInit).isParameterDefinition(node1.asParameter()) or
        capturedDef.(SsaExplicitUpdate).getDefiningExpr().(VariableAssign).getSource() = node1.asExpr() or
        capturedDef.(SsaExplicitUpdate).getDefiningExpr().(AssignOp) = node1.asExpr()
      )
    )
  }

  /**
   * Holds if data can flow from `node1` to `node2` through a static field or
   * variable capture.
   */
  predicate jumpStep(Node node1, Node node2) {
    staticFieldStep(node1, node2) or
    variableCaptureStep(node1, node2)
  }
