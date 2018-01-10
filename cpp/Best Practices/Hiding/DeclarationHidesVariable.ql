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
 * @name Declaration hides variable
 * @description A local variable hides another local variable from a surrounding scope. This may be confusing. Consider renaming one of the variables.
 * @kind problem
 * @problem.severity recommendation
 * @precision high
 * @id cpp/declaration-hides-variable
 * @tags maintainability
 *       readability
 */
import default

import Best_Practices.Hiding.Shadowing

from LocalVariable lv1, LocalVariable lv2
where shadowing(lv1, lv2) and
      not lv1.getParentScope().(Block).isInMacroExpansion() and
      not lv2.getParentScope().(Block).isInMacroExpansion()
select lv1, "Variable " + lv1.getName() +
            " hides another variable of the same name (on $@).",
            lv2, "line " + lv2.getLocation().getStartLine().toString()
