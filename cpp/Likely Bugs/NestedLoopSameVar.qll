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

/**
 * Provides the implementation of the query 'Nested loops with same variable'.
 */

import cpp

/**
 * Holds if `inner` and `outer` are nested for statements that
 * use the same loop variable `iteration`.  
 */
predicate nestedForViolation(ForStmt inner, Variable iteration, ForStmt outer) {
  iteration = inner.getAnIterationVariable() and
  iteration = outer.getAnIterationVariable() and
  exists(inner.getInitialization()) and
  inner.getParent+() = outer and
  inner.getASuccessor+() = outer.getCondition()
}
