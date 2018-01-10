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
 * @name Declaration hides parameter
 * @description A local variable hides a parameter. This may be confusing. Consider renaming one of them.
 * @kind problem
 * @problem.severity recommendation
 * @precision very-high
 * @id cpp/declaration-hides-parameter
 * @tags maintainability
 *       readability
 */
import default


/* Names of parameters in the implementation of a function.
   Notice that we need to exclude parameter names used in prototype
   declarations and only include the ones from the actual definition.
   We also exclude names from functions that have multiple definitions.
   This should not happen in a single application but since we
   have a system wide view it is likely to happen for instance for
   the main function. */
ParameterDeclarationEntry functionParameterNames(Function f, string name) {
  exists(FunctionDeclarationEntry fe |
    result.getFunctionDeclarationEntry() = fe
    and fe.getFunction() = f
    and fe.getLocation() = f.getDefinitionLocation()
    and strictcount(f.getDefinitionLocation()) = 1
    and result.getName() = name
  )
}

from Function f, LocalVariable lv, ParameterDeclarationEntry pde
where f = lv.getFunction() and
      pde = functionParameterNames(f, lv.getName()) and
      not lv.isInMacroExpansion()
select lv, "This local variable hides a $@.", pde, "parameter of the same name"
