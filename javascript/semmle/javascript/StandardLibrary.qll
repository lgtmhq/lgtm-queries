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
class CallToObjectDefineProperty extends CallExpr {
  CallToObjectDefineProperty() {
    exists (GlobalVariable theObject, PropAccess objDefProp |
      getCallee().stripParens() = objDefProp and
      objDefProp.getBase().stripParens() = theObject.getAnAccess() and
      theObject.getName() = "Object" and
      objDefProp.getPropertyName() = "defineProperty"
    )
  }

  /** Gets the expression denoting the object on which the property is defined. */
  Expr getBaseObject() {
    result = getArgument(0)
  }

  /** Gets the name of the property being defined, if it can be determined. */
  string getPropertyName() {
    result = getArgument(1).(ConstantString).getStringValue()
  }

  /** Gets the expression denoting the descriptor of the property being defined. */
  Expr getPropertyDescriptor() {
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
    getReceiver().accessesGlobal("JSON") and
    getMethodName() = "parse"
  }
}
