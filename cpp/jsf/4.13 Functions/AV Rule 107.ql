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
 * @name Function declared in block
 * @description Functions should always be declared at file scope. It is confusing to declare a function at block scope, and the visibility of the function is not what would be expected.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @id cpp/function-in-block
 * @tags maintainability
 *       readability
 */
import default

from DeclStmt ds
where ds.getADeclaration() instanceof Function
      and not ds.isInMacroExpansion()
      and not exists(MacroInvocation mi | mi.getLocation() = ds.getADeclarationEntry().getLocation())
select ds, "Functions should always be declared at file scope, not inside blocks."
