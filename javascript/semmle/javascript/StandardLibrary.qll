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

/** Provides classes for working with standard library objects. */

import javascript

/**
 * A call to `Object.defineProperty`.
 */
class CallToObjectDefineProperty extends DataFlow::MethodCallNode {
  CallToObjectDefineProperty() {
    exists (GlobalVariable obj |
      obj.getName() = "Object" and
      astNode.calls(obj.getAnAccess(), "defineProperty")
    )
  }

  /** Gets the data flow node denoting the object on which the property is defined. */
  DataFlow::Node getBaseObject() {
    result = getArgument(0)
  }

  /** Gets the name of the property being defined, if it can be determined. */
  string getPropertyName() {
    result = getArgument(1).asExpr().(ConstantString).getStringValue()
  }

  /** Gets the data flow node denoting the descriptor of the property being defined. */
  DataFlow::Node getPropertyDescriptor() {
    result = getArgument(2)
  }
}

/**
 * A direct call to `eval`.
 */
class DirectEval extends CallExpr {
  DirectEval() {
    getCallee().(GlobalVarAccess).getName() = "eval"
  }

  /** Holds if this call could affect the value of `lv`. */
  predicate mayAffect(LocalVariable lv) {
    getParent+() = lv.getScope().getScopeElement()
  }
}

/**
 * A call to `JSON.parse`.
 */
class JsonParseCall extends MethodCallExpr {
  JsonParseCall() {
    this = DataFlow::globalVarRef("JSON").getAMemberCall("parse").asExpr()
  }
}

/**
 * Flow analysis for `this` expressions inside a function that is called with
 * `Array.prototype.map` or a similar Array function that binds `this`.
 *
 * However, since the function could be invoked in another way, we additionally
 * still infer the ordinary abstract value.
 */
private class AnalyzedThisInArrayIterationFunction extends AnalyzedValueNode {

  AnalyzedValueNode thisSource;

  override ThisExpr astNode;

  AnalyzedThisInArrayIterationFunction() {
    exists(DataFlow::MethodCallNode bindingCall, string name |
      name = "filter" or
      name = "forEach" or
      name = "map" or
      name = "some" or
      name = "every" |
      name = bindingCall.getMethodName() and
      2 = bindingCall.getNumArgument() and
      astNode.getBinder() = bindingCall.getCallback(0).getFunction() and
      thisSource = bindingCall.getArgument(1)
    )
  }

  override AbstractValue getALocalValue() {
    result = thisSource.getALocalValue() or
    result = AnalyzedValueNode.super.getALocalValue()
  }

}
