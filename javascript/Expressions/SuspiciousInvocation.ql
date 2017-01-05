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
 * @name Invocation of non-function
 * @description Trying to invoke a value that is not a function will result
 *              in a runtime exception.
 * @kind problem
 * @problem.severity error
 * @tags correctness
 */

import javascript
import semmle.javascript.flow.Analysis
private import semmle.javascript.flow.InferredTypes

from InvokeExpr invk, AnalysedFlowNode callee
where callee = invk.getCallee() and
      forex (InferredType tp | tp = callee.getAType() | tp != TTFunction() and tp != TTClass())
select invk, "Callee is not a function: it has type " + callee.ppTypes() + "."