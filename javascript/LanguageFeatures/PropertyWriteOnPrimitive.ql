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
 * @name Assignment to property of primitive value
 * @description Assigning to a property of a primitive value has no effect
 *              and may trigger a runtime error.
 * @kind problem
 * @problem.severity error
 * @tags correctness
 *       language-features
 * @precision high
 */

import javascript
private import semmle.javascript.flow.Analysis
private import semmle.javascript.flow.InferredTypes

/** Gets a description of the property written by `pwn`. */
string describeProp(PropWriteNode pwn) {
  result = "property " + pwn.getPropertyName()
  or
  not exists(pwn.getPropertyName()) and result = "a property"
}

from PropWriteNode pwn, AnalysedFlowNode base
where base = pwn.getBase() and
      base.hasFlow() and
      forall (InferredType tp | tp = base.getAType() |
        tp instanceof PrimitiveType and
        // assignments on `null` and `undefined` are covered by
        // the query 'Property access on null or undefined'
        tp != TTNull() and tp != TTUndefined()
      )
select base, "Assignment to " + describeProp(pwn) +
             " of a primitive value with type " + base.ppTypes() + "."
