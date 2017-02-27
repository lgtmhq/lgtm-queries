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
 * @name Module is imported with 'import' and 'import from'
 * @description A module is imported with the "import" and "import from" statements
 * @kind problem
 * @tags maintainability
 * @problem.severity recommendation
 * @sub-severity high
 * @precision very-high
 */

import python

predicate import_and_import_from(Import i1, Import i2, Module m) {
		i1.getEnclosingModule() = i2.getEnclosingModule() and
		exists (ImportExpr e1, ImportExpr e2, ImportMember im |
		        e1 = i1.getAName().getValue() and im = i2.getAName().getValue() and e2 = im.getModule() |
		        e1.getName() = m.getName() and e2.getName() = m.getName()
    )
}

from Stmt i1, Stmt i2, Module m
where import_and_import_from(i1, i2, m)
select i1, "Module '" + m.getName() + "' is imported with both 'import' and 'import from'"
