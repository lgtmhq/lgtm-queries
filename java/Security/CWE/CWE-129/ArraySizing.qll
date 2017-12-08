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

import java
import semmle.code.java.security.DataFlow
private import BoundingChecks

/**
 * If the `Array` accessed by the `ArrayAccess` is a fixed size, return the array size.
 */
private int fixedArraySize(ArrayAccess arrayAccess) {
  result = arrayAccess.getArray().(VarAccess).getVariable().getAnAssignedValue()
                      .(ArrayCreationExpr).getFirstDimensionSize()
}

/**
 * Holds if an `ArrayIndexOutOfBoundsException` is ever caught.
 */
private predicate arrayIndexOutOfBoundExceptionCaught(ArrayAccess arrayAccess) {
  exists(TryStmt ts, CatchClause cc |
    (
      ts.getBlock().getAChild*() = arrayAccess.getEnclosingStmt() or
      ts.getAResourceDecl().getAChild*() = arrayAccess.getEnclosingStmt() or
      ts.getAResourceExpr().getAChildExpr*() = arrayAccess
    ) and
    cc = ts.getACatchClause() |
    cc.getVariable().getType().(RefType).hasQualifiedName("java.lang", "ArrayIndexOutOfBoundsException")
  )
}

/**
 * A pointless loop, of the type seen frequently in Juliet tests, of the form:
 *
 * ```
 *   while(true) {
 *     ...
 *     break;
 *   }
 * ```
 */
class PointlessLoop extends WhileStmt {
  PointlessLoop() {
    getCondition().(BooleanLiteral).getBooleanValue() = true and
    // The only `break` must be the last statement.
    forall(BreakStmt break |
      break.(JumpStmt).getTarget() = this |
      this.getStmt().(Block).getLastStmt() = break
    ) and
    // No `continue` statements.
    not exists(ContinueStmt continue |
      continue.(JumpStmt).getTarget() = this
    )
  }
}

/**
 * An `ArrayAccess` for which we can determine whether the index is appropriately bound checked.
 *
 * We only consider first dimension array accesses, and we only consider indices in loops, if it's
 * obvious that the loop only executes once.
 */
class CheckableArrayAccess extends ArrayAccess {
  CheckableArrayAccess() {
    /*
     * We are not interested in array accesses that don't access the first dimension.
     */
    not this.getArray() instanceof ArrayAccess and
    /*
     * Array accesses within loops can make it difficult to verify whether the index is checked
     * prior to access. Ignore "pointless" loops of the sort found in Juliet test cases.
     */
    not exists(LoopStmt loop |
      loop.getBody().getAChild*() = getEnclosingStmt() and
      not loop instanceof PointlessLoop
    ) and
    // The possible exception is not caught
    not arrayIndexOutOfBoundExceptionCaught(this)
  }

  /**
   * Holds if we believe this indexing expression will throw an `ArrayIndexOutOfBoundsException` due
   * to the index flowing from `source` being out of bounds.
   */
  predicate canThrowOutOfBounds(FlowSource source) {
    source.flowsTo(getIndexExpr()) and source != getIndexExpr() and
    not (
      (
        // The input has a lower bound.
        source.(BoundedFlowSource).lowerBound() >= 0 or
        // There is a condition dominating this expression ensuring that the index is >= 0.
        lowerBound(getIndexExpr()) >= 0
      )
      and
      (
        // The input has an upper bound, and the array has a fixed size, and that fixed size is less.
        source.(BoundedFlowSource).upperBound() < fixedArraySize(this) or
        // There is a condition dominating this expression that ensures the index is less than the length.
        lessthanLength(this)
      )
    )
  }

  /**
   * Holds if we believe this indexing expression will throw an `ArrayIndexOutOfBoundsException` due
   * to the array being initialized with a size flowing from `source`, which may be zero.
   */
  predicate canThrowOutOfBoundsDueToEmptyArray(FlowSource source, ArrayCreationExpr arrayCreation) {
    /*
     * Find an `ArrayCreationExpr` for the array used in this indexing operation.
     */
    exists(VariableAssign assign |
      assign.getSource() = arrayCreation and
      defUsePair(assign, this.getArray())
    ) and
    /*
     * If the array access is protected by a conditional that verifies the index is less than the array
     * length, then the array will never be accessed if the size is zero.
     */
    not lessthanLength(this) and
    /*
     * Determine if the size expression for the `ArrayCreationExpr` flows from the source, and is
     * not, itself, checked to be greater than zero.
     */
    exists(Expr sizeExpr |
      /*
       * Find a case where an array is constructed where the size of the first dimension is determined by
       * some `UserInput`. If this size hasn't been verified, then it could be zero.
       */
      sizeExpr = arrayCreation.getDimension(0) and source.flowsTo(sizeExpr) and
      /*
       * Verify that the size expression is never checked to be greater than 0.
       */
      not lowerBound(sizeExpr) > 0 and
      // There is not a fixed lower bound which is greater than zero.
      not source.(BoundedFlowSource).lowerBound() > 0
    )
  }
}

/**
 * A source of "flow" which has an upper or lower bound.
 */
abstract class BoundedFlowSource extends FlowSource {

  /**
   * Return a lower bound for the input, if possible.
   */
  abstract int lowerBound();

  /**
   * Return an upper bound for the input, if possible.
   */
  abstract int upperBound();

  /**
   * Flow sources with an upper or lower bound are generally harder to track accurately through
   * possible modifications, so specifically exclude "modifying" `FlowExpr`s from the flow graph.
   */
  predicate isExcluded(FlowExpr flowExpr) {
    flowExpr instanceof AddExpr or
    flowExpr instanceof LogicExpr or
    flowExpr instanceof BitwiseExpr or
    /*
     * Also ignore expressions which stash values into a store, as we don't track which index
     * the values are read from.
     */
    flowExpr instanceof ArrayCreationExpr or
    flowExpr instanceof ArrayInit or
    flowExpr instanceof ArrayAccess
  }

  /**
   * Return a description for this flow source, suitable for putting in an alert message.
   */
  abstract string getDescription();
}

/**
 * Input that is constructed using a `Random` value.
 */
class RandomValueFlowSource extends BoundedFlowSource {
  RandomValueFlowSource() {
    exists(RefType random, MethodAccess nextAccess |
      random.hasQualifiedName("java.util", "Random") |
      nextAccess.getCallee().getDeclaringType().getAnAncestor() = random and
      nextAccess.getCallee().getName().matches("next%") and
      nextAccess = this
    )
  }

  int lowerBound() {
    // If this call is to `nextInt()`, the lower bound is zero.
    this.(MethodAccess).getCallee().hasName("nextInt") and
    this.(MethodAccess).getNumArgument() = 1 and
    result = 0
  }

  int upperBound() {
    /*
     * If this call specified an argument to `nextInt()`, and that argument is a compile time constant,
     * it forms the upper bound.
     */
    this.(MethodAccess).getCallee().hasName("nextInt") and
    this.(MethodAccess).getNumArgument() = 1 and
    result = this.(MethodAccess).getArgument(0).(CompileTimeConstantExpr).getIntValue()
  }

  string getDescription() {
    result = "Random value"
  }
}

/**
 * A compile time constant expression that evaluates to a numeric type.
 */
class NumericLiteralFlowSource extends BoundedFlowSource {
  NumericLiteralFlowSource() {
    this instanceof CompileTimeConstantExpr and
    exists(this.(CompileTimeConstantExpr).getIntValue())
  }

  int lowerBound() {
    result = this.(CompileTimeConstantExpr).getIntValue()
  }

  int upperBound() {
    result = this.(CompileTimeConstantExpr).getIntValue()
  }

  string getDescription() {
    result = "Literal value " + this.(CompileTimeConstantExpr).getIntValue()
  }
}
