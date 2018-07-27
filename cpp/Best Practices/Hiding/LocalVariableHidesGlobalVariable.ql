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
 * @name Local variable hides global variable
 * @description A local variable or parameter that hides a global variable of the same name. This may be confusing. Consider renaming one of the variables.
 * @kind problem
 * @problem.severity warning
 * @precision very-high
 * @id cpp/local-variable-hides-global-variable
 * @tags maintainability
 *       readability
 */
import cpp

class LocalVariableOrParameter extends VariableDeclarationEntry {
  LocalVariableOrParameter() {
    this.getVariable() instanceof LocalScopeVariable and
    (
      // we only need to report parameters hiding globals when the clash is with the parameter
      // name as used in the function definition.  The parameter name used in any other function
      // declaration is harmless.
      this instanceof ParameterDeclarationEntry
      implies
      exists(this.(ParameterDeclarationEntry).getFunctionDeclarationEntry().getBlock())
    )
  }

  string type() {
    if this.getVariable() instanceof Parameter
    then result = "Parameter "
    else result = "Local variable "
  }
}

from LocalVariableOrParameter lv, GlobalVariable gv
where lv.getName() = gv.getName() and
      lv.getFile() = gv.getFile()
select lv, lv.type() + gv.getName() + " hides $@ with the same name.", gv, "a global variable"
