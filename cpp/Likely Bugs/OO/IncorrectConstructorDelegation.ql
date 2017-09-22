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
 * @name Incorrect constructor delegation
 * @description A constructor in C++ cannot delegate part of the object
 *              initialization to another by calling it. This is likely to
 *              leave part of the object uninitialized.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @tags maintainability
 *       readability
 *       language-features
 */

import default

from FunctionCall call
where call.getTarget() = call.getEnclosingFunction().(Constructor).getDeclaringType().getAConstructor()
  and call.getParent() instanceof ExprStmt
select call, "The constructor " + call.getTarget().getName() +
  " may leave the instance uninitialized, as it tries to delegate to another constructor."
