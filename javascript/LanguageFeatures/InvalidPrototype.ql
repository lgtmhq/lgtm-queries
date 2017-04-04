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

/**
 * @name Invalid prototype value
 * @description An attempt to use a value that is not an object or 'null' as a
 *              prototype will either be ignored or result in a runtime error.
 * @kind problem
 * @problem.severity error
 * @tags correctness
 *       language-features
 * @precision high
 */

import javascript
private import semmle.javascript.flow.Analysis
private import semmle.javascript.flow.InferredTypes

/**
 * Holds if the value of `e` is used as a prototype object.
 */
predicate isProto(AnalyzedFlowNode e) {
  // `o.__proto__ = e`, `{ __proto__: e }`, ...
  e = any(PropWriteNode pwn | pwn.getPropertyName() = "__proto__").getRhs()
  or
  exists (MethodCallExpr me, Expr recv, string n |
    recv = me.getReceiver() and n = me.getMethodName() |
    exists (GlobalVarAccess obj | obj = recv.stripParens() and obj.getName() = "Object" |
      // Object.create(e)
      n = "create" and e = me.getArgument(0) or
      // Object.setPrototypeOf(o, e)
      n = "setPrototypeOf" and e = me.getArgument(1)
    ) or
    // e.isPrototypeOf(o)
    e = recv and n = "isPrototypeOf"
  )
}

from AnalyzedFlowNode proto
where isProto(proto) and
      proto.hasFlow() and
      forall (InferredType tp | tp = proto.getAType() |
        tp instanceof PrimitiveType and tp != TTNull()
      )
select proto, "Values of type " + proto.ppTypes() + " cannot be used as prototypes."
