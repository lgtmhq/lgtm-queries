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
 * @name Property access on null or undefined
 * @description Trying to access a property of "null" or "undefined" will result
 *              in a runtime exception.
 * @kind problem
 * @problem.severity error
 * @id js/property-access-on-non-object
 * @tags correctness
 *       external/cwe/cwe-476
 * @precision high
 */

import javascript
import semmle.javascript.flow.Analysis
private import semmle.javascript.flow.InferredTypes

from PropAccess pacc, AnalyzedFlowNode base
where base = pacc.getBase() and
      base.hasFlow() and
      forall (InferredType tp | tp = base.getAType() | tp = TTNull() or tp = TTUndefined())
select pacc, "The base expression of this property access is always " + base.ppTypes() + "."