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
 * @name Use of call stack introspection in strict mode
 * @description Accessing properties 'arguments.caller', 'arguments.callee',
 *              'Function.prototype.caller' or 'Function.prototype.arguments'
 *              in strict mode will cause a runtime error.
 * @kind problem
 * @problem.severity error
 * @tags correctness
 *       language-features
 * @precision high
 */

import javascript
import semmle.javascript.flow.Analysis

/**
 * Holds if it is illegal to access property `prop` on `baseVal` in strict-mode
 * code; `baseDesc` is a description of `baseVal` used in the alert message.
 */
predicate illegalPropAccess(AbstractValue baseVal, string baseDesc, string prop) {
  baseVal instanceof AbstractArguments and baseDesc = "arguments" and
  (prop = "caller" or prop = "callee")
  or
  baseVal instanceof AbstractFunction and baseDesc = "Function.prototype" and
  (prop = "caller" or prop = "arguments")
}

from PropAccess acc, AnalyzedFlowNode baseNode, string base, string prop
where baseNode = acc.getBase() and prop = acc.getPropertyName() and
      acc.getContainer().isStrict() and
      illegalPropAccess(baseNode.getAValue(), base, prop) and
      forall (AbstractValue av | av = baseNode.getAValue() | illegalPropAccess(av, _, prop))
select acc, "Strict mode code cannot use " + base + "." + prop + "."