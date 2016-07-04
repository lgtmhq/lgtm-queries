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
 * Simple intra-procedural flow analysis for inferring types and
 * Boolean values of nodes in a data flow graph.
 */

import javascript
import AbstractValues
import InferredTypes
private import AbstractValuesImpl

/**
 * A data flow node for which analysis results are available.
 */
class AnalysedFlowNode extends DataFlowNode {
  /**
   * An abstract value that this node may evaluate to at runtime.
   */
  cached
  AbstractValue getAValue() {
    // model flow from other nodes; we do not currently
    // feed back the results from the (value) flow analysis into
    // the control flow analysis, so all flow predecessors are
    // considered as sources
    result = flowPred().(AnalysedFlowNode).getAValue() or
    // model flow that isn't captured by the data flow graph
    exists (DataFlowIncompleteness cause |
      isIncomplete(cause) and result = indefiniteAbstractValue(cause)
    )
  }

  /**
   * A type inferred for this node.
   */
  InferredType getAType() {
    result = getAValue().getType()
  }

  /**
   * The unique Boolean value that this node evaluates to, if any.
   */
  boolean getTheBooleanValue() {
    forex (boolean bv | bv = getAValue().getBooleanValue() | result = bv)
  }

  /**
   * Pretty-print all types inferred for this node as a comma-separated list, with
   * the last comma being spelled "or".
   *
   * This is useful for violation message, since some expressions (in
   * particular addition) may have more than one inferred type.
   */
  string ppTypes() {
    exists (int n | n = getNumTypes() |
      // inferred no types
      n = 0 and result = "" or
      // inferred a single type
      n = 1 and result = getAType() or
      // inferred all types
      n = count(InferredType it) and result = ppAllTypeTags() or
      // the general case: more than one type, but not all types
      // first pretty-print as a comma separated list, then replace last comma by "or"
      result = (getType(1) + ", " + ppTypes(2)).regexpReplaceAll(", ([^,]++)$", " or $1")
    )
  }

  /**
   * Helper predicate to get the i-th type inferred for this node in lexicographical
   * order.
   */
  private string getType(int i) {
    result = rank[i](string tp | tp = getAType())
  }

  private int getNumTypes() {
    result = count(getAType())
  }

  /**
   * Helper predicate to produce a comma-separated list of all types inferred for this node,
   * in lexicographical order, starting with the `i`-th type (1-based), where `i` ranges
   * between two and one less than the total number of types. The single-type case and
   * the all-types case are handled specially above.
   */
  private string ppTypes(int i) {
    exists (int n | n = getNumTypes() and n in [2..count(InferredType it)-1] |
      i = n and result = getType(i) or
      i in [2..n-1] and result = getType(i) + ", " + ppTypes(i+1)
    )
  }
}

/**
 * Flow analysis for Boolean literals.
 */
library
class BooleanLiteralSource extends AnalysedFlowNode, @booleanliteral {
  AbstractValue getAValue() {
    exists (string v | v = this.(Literal).getValue() |
      v = "true" and result = theAbstractTrueValue() or
      v = "false" and result = theAbstractFalseValue()
    )
  }
}

/**
 * Flow analysis for number literals.
 */
library
class NumberLiteralSource extends AnalysedFlowNode, @numberliteral {
  private predicate isZero() {
    exists (float v | v = this.(Literal).getValue().toFloat() | v = 0.0 or v = -0.0)
  }

  AbstractValue getAValue() {
    if isZero() then
      result = theAbstractZeroValue()
    else
      result = theAbstractNonZeroValue()
  }
}

/**
 * Flow analysis for string literals.
 */
library
class StringLiteralSource extends AnalysedFlowNode, @stringliteral {
  AbstractValue getAValue() {
    exists (string v | v = this.(Literal).getValue() |
      if v = "" then
        result = theAbstractEmptyValue()
      else if exists(v.toFloat()) then
        result = theAbstractNumStringValue()
      else
        result = theAbstractOtherStringValue()
    )
  }
}

/**
 * Flow analysis for template literals.
 */
library
class TemplateLiteralSource extends AnalysedFlowNode, @templateliteral {
  AbstractValue getAValue() { result = abstractValueOfType("string") }
}

/**
 * Flow analysis for regular expression literals.
 */
library
class RegExpLiteralSource extends AnalysedFlowNode, @regexpliteral {
  AbstractValue getAValue() { result = theAbstractObjectValue() }
}

/**
 * Flow analysis for the null literal.
 */
library
class NullLiteralSource extends AnalysedFlowNode, @nullliteral {
  AbstractValue getAValue() { result = theAbstractNullValue() }
}

/**
 * Flow analysis for object expressions.
 */
library
class ObjectExprSource extends AnalysedFlowNode, @objexpr {
  AbstractValue getAValue() { result = theAbstractObjectValue() }
}

/**
 * Flow analysis for array expressions.
 */
library
class ArrayExprSource extends AnalysedFlowNode, @arrayexpr {
  AbstractValue getAValue() { result = theAbstractObjectValue() }
}

/**
 * Flow analysis for array comprehensions.
 */
library
class ArrayComprehensionExprSource extends AnalysedFlowNode, @arraycomprehensionexpr {
  AbstractValue getAValue() { result = theAbstractObjectValue() }
}

/**
 * Flow analysis for function expressions.
 */
library
class FunctionSource extends AnalysedFlowNode, @function {
  AbstractValue getAValue() { result = theAbstractFunctionValue() }
}

/**
 * Flow analysis for class declarations.
 */
library
class ClassExprSource extends AnalysedFlowNode, @classdecl {
  AbstractValue getAValue() { result = theAbstractClassValue() }
}

/**
 * Flow analysis for `this`.
 */
library
class ThisSource extends AnalysedFlowNode, @thisexpr {
  AbstractValue getAValue() {
    result = indefiniteAbstractValue("call")
  }
}

/**
 * Flow analysis for `super`.
 */
library
class SuperSource extends AnalysedFlowNode, @superexpr {
  AbstractValue getAValue() {
    result = indefiniteAbstractValue("call")
  }
}

/**
 * Flow analysis for arithmetic expressions.
 */
library
class ArithmeticSource extends AnalysedFlowNode, @binaryexpr {
  ArithmeticSource() { this instanceof ArithmeticExpr }

  AbstractValue getAValue() { result = abstractValueOfType("number") }
}

/**
 * Could `afn` evaluate to a value that, when converted to a primitive value,
 * yields a string?
 */
private predicate convertsToString(AnalysedFlowNode afn) {
  afn.getAValue().toPrimitive().getType() = "string"
}

/**
 * Could `afn` evaluate to a value that, when converted to a primitive value,
 * yields a non-string?
 */
private predicate convertsToNonString(AnalysedFlowNode afn) {
  afn.getAValue().toPrimitive().getType() != "string"
}

/**
 * Is `e` a `+` or `+=` expression that could be interpreted as a string append
 * (as opposed to a numeric addition) at runtime?
 */
private predicate isStringAppend(Expr e) {
  (e instanceof AddExpr or e instanceof AssignAddExpr) and
  convertsToString(e.getAChild())
}

/**
 * Is `e` a `+` or `+=` expression that could be interpreted as a numeric addition
 * (as opposed to a string append) at runtime?
 */
private predicate isAddition(Expr e) {
  (e instanceof AddExpr or e instanceof AssignAddExpr) and
  convertsToNonString(e.getChild(0)) and
  convertsToNonString(e.getChild(1))
}

/**
 * Flow analysis for addition.
 */
library
class AddExprSource extends ArithmeticSource, @addexpr {
  AbstractValue getAValue() {
    isStringAppend(this) and result = abstractValueOfType("string") or
    isAddition(this) and result = abstractValueOfType("number")
  }
}

/**
 * Flow analysis for bitwise expressions.
 */
library
class BitwiseExprSource extends AnalysedFlowNode, @expr {
  BitwiseExprSource() { this instanceof BitwiseExpr }

  AbstractValue getAValue() { result = abstractValueOfType("number") }
}

/**
 * Flow analysis for `new`.
 */
library
class NewSource extends AnalysedFlowNode, @newexpr {
  AbstractValue getAValue() {
    result = abstractValueOfType("function") or
    result = abstractValueOfType("date") or
    result = abstractValueOfType("object")
  }
}

/**
 * Flow analysis for `void` expressions.
 */
library
class VoidSource extends AnalysedFlowNode, @voidexpr {
  AbstractValue getAValue() { result = theAbstractUndefinedValue() }
}

/**
 * Flow analysis for `typeof` expressions.
 */
library
class TypeofSource extends AnalysedFlowNode, @typeofexpr {
  AbstractValue getAValue() { result = theAbstractOtherStringValue() }
}

/**
 * Flow analysis for comparison expressions.
 */
library
class ComparisonSource extends AnalysedFlowNode, @comparison {
  AbstractValue getAValue() { result = abstractValueOfType("boolean") }
}

/**
 * Flow analysis for `in` expressions.
 */
library
class InSource extends AnalysedFlowNode, @inexpr {
  AbstractValue getAValue() { result = abstractValueOfType("boolean") }
}

/**
 * Flow analysis for `instanceof` expressions.
 */
library
class InstanceofSource extends AnalysedFlowNode, @instanceofexpr {
  AbstractValue getAValue() { result = abstractValueOfType("boolean") }
}

/**
 * Flow analysis for increment and decrement expressions.
 */
library
class UpdateSource extends AnalysedFlowNode, @updateexpr {
  AbstractValue getAValue() { result = abstractValueOfType("number") }
}

/**
 * Flow analysis for logical negation.
 */
library
class LogNotSource extends AnalysedFlowNode, @lognotexpr {
  AbstractValue getAValue() {
    exists (AbstractValue op | op = this.(UnaryExpr).getOperand().(AnalysedFlowNode).getAValue() |
      exists (boolean bv | bv = op.getBooleanValue() |
        bv = true and result = theAbstractFalseValue() or
        bv = false and result = theAbstractTrueValue()
      )
    )
  }
}

/**
 * Flow analysis for arithmetic negation.
 */
library
class NegExprSource extends AnalysedFlowNode, @negexpr {
  AbstractValue getAValue() { result = abstractValueOfType("number") }
}

/**
 * Flow analysis for unary plus.
 */
library
class PlusExprSource extends AnalysedFlowNode, @plusexpr {
  AbstractValue getAValue() { result = abstractValueOfType("number") }
}

/**
 * Flow analysis for bitwise negation.
 */
library
class BitNotSource extends AnalysedFlowNode, @bitnotexpr {
  AbstractValue getAValue() { result = abstractValueOfType("number") }
}

/**
 * Flow analysis for `delete` expressions.
 */
library
class DeleteSource extends AnalysedFlowNode, @deleteexpr {
  AbstractValue getAValue() { result = abstractValueOfType("boolean") }
}

/**
 * Flow analysis for compound assignments.
 */
library
class CompoundAssignSource extends AnalysedFlowNode, @assignment {
  CompoundAssignSource() { this instanceof CompoundAssignExpr }

  AbstractValue getAValue() { result = abstractValueOfType("number") }
}

/**
 * Flow analysis for add-assign.
 */
library
class AddAssignSource extends CompoundAssignSource, @assignaddexpr {
  AbstractValue getAValue() {
    isStringAppend(this) and result = abstractValueOfType("string") or
    isAddition(this) and result = abstractValueOfType("number")
  }
}

/**
 * Flow analysis for local variables that are used before being initialised.
 */
library
class UninitialisedVarAccessSource extends AnalysedFlowNode, @cfg_node {
  UninitialisedVarAccessSource() {
    this instanceof VarUse and
    exists (LocalVariable lv |
      lv = this.(VarUse).getVariable() and not guaranteedToBeInitialised(lv) |
      lv.isCaptured() or
      exists (BasicBlock bb | bb = this.(Expr).getEnclosingFunction().getEntryBB() |
        bb.localIsLiveAtEntry((PurelyLocalVariable) lv, (VarUse)this)
      )
    )
  }

  AbstractValue getAValue() { result = AnalysedFlowNode.super.getAValue() or result = theAbstractUndefinedValue() }
}

/**
 * Identify local variables that can never be observed in their uninitialised state.
 */
private predicate guaranteedToBeInitialised(LocalVariable v) {
  // function declarations can never be uninitialised due to hoisting
  exists (FunctionDeclStmt fd | v = fd.getVariable()) or
  // parameters also can never be uninitialised
  exists (Parameter p | v = p.getAVariable())
}

/**
 * Flow analysis for the `arguments` variable.
 */
library
class ArgumentsSource extends UninitialisedVarAccessSource {
  ArgumentsSource() {
    this.(VarAccess).getVariable() instanceof ArgumentsObject
  }

  AbstractValue getAValue() { result = theAbstractObjectValue() }
}

/**
 * Helper predicate for modelling Node.js builtins.
 */
private predicate nodeBuiltins(Variable var, AbstractValue av) {
  var.getScope() instanceof ModuleScope and
  exists (string name | name = var.getName() |
    name = "require" and av = indefiniteAbstractValue("heap") or

    (name = "module" or name = "exports") and av = theAbstractObjectValue() or

    (name = "__filename" or name = "__dirname") and
    (av = theAbstractNumStringValue() or av = theAbstractOtherStringValue())  )
}

/**
 * Flow analysis for Node.js builtins.
 */
library
class NodeBuiltinSource extends AnalysedFlowNode, @varaccess {
  NodeBuiltinSource() {
    nodeBuiltins(this.(VarAccess).getVariable(), _)
  }

  AbstractValue getAValue() {
    result = AnalysedFlowNode.super.getAValue() or
    nodeBuiltins(getVariable(), result)
  }

  Variable getVariable() { result = this.(VarAccess).getVariable() }
}

/**
 * Flow analysis for `undefined` (assuming it is not redefined).
 */
library
class UndefinedSource extends AnalysedFlowNode, @varaccess {
  UndefinedSource() { this.(GlobalVarAccess).getName() = "undefined" }

  AbstractValue getAValue() { result = theAbstractUndefinedValue() }
}
