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
 * @name Default parameter references nested function
 * @description If a default parameter value references a function that is nested inside the
 *              function to which the parameter belongs, a runtime error will occur, since
 *              the function is not yet defined at the point where it is referenced.
 * @kind problem
 * @problem.severity error
 * @id js/nested-function-reference-in-default-parameter
 * @tags reliability
 *       correctness
 * @precision very-high
 */

import javascript

/**
 * Holds if `va` references function `inner`, which is nested inside function `outer`.
 */
predicate accessToNestedFunction(VarAccess va, FunctionDeclStmt inner, Function outer) {
  va.getVariable() = inner.getVariable() and
  inner.getEnclosingContainer() = outer
}

from Function f, VarAccess va, FunctionDeclStmt g
where accessToNestedFunction(va, g, f) and
      va.getParentExpr*() = f.getAParameter().getDefault()
select va, "This expression refers to $@ before it is defined.", g, g.getName()