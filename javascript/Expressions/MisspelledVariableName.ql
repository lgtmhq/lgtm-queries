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
 * @name Misspelled variable name
 * @description Misspelling a variable name implicitly introduces a global
 *              variable, which may not lead to a runtime error, but is
 *              likely to give wrong results.
 * @kind problem
 * @problem.severity warning
 * @id js/misspelled-variable-name
 * @tags maintainability
 *       readability
 *       correctness
 * @precision very-high
 */

import Misspelling

from GlobalVarAccess gva, VarDecl lvd
where misspelledVariableName(gva, lvd)
select gva, "'" + gva + "' may be a typo for variable $@.", lvd, lvd.getName()
