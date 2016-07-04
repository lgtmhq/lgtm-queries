// Copyright 2016 Semmle Ltd.
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
 * @name Cyclic import
 * @description Module forms part of an import cycle, thereby indirectly importing itself.
 * @kind problem
 * @problem.severity warning
 */

import python
import Cyclic

from PythonModuleObject m1, PythonModuleObject m2, Stmt imp
where 
  imp.getEnclosingModule() = m1.getModule()
  and stmt_imports(imp) = m2
  and circular_import(m1, m2)
  and m1 != m2
  // this query finds all cyclic imports that are *not* flagged by ModuleLevelCyclicImport
  and not failing_import_due_to_cycle(m2, m1, _, _, _, _)
  and not exists(If i | i.isNameEqMain() and i.contains(imp))
select imp, "Import of module $@ begins an import cycle.", m2, m2.getName()

