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
 * @name Use of an undefined global variable
 * @description Using a global variable before it is initialized causes an exception.
 * @kind problem
 * @problem.severity error
 */

import python
import Variables.MonkeyPatched

predicate guarded_against_name_error(Name u) {
    exists(Try t | t.getBody().getAnItem().contains(u) |
                   ((Name)((ExceptStmt)t.getAHandler()).getType()).getId() = "NameError"
          )
    or
    exists(ConditionBlock guard, BasicBlock controlled, Call globals |
        guard.getLastNode().getNode().contains(globals) or
        guard.getLastNode().getNode() = globals |
        globals.getFunc().(Name).getId() = "globals" and
        guard.controls(controlled, _) and
        controlled.contains(u.getAFlowNode())
    )
}

predicate contains_unknown_import_star(Module m) {
     exists(ImportStar imp | imp.getScope() = m |
        not exists(ModuleObject imported | imported.importedAs(imp.getImportedModuleName()))
        or
        exists(ModuleObject imported | 
            imported.importedAs(imp.getImportedModuleName()) |
            not imported.exportsComplete()
        )
    )
}

predicate undefined_use_in_function(Name u) {
    exists(Function f | u.getScope().getScope*() = f and
        /* Either function is a method or inner function or it is live at the end of the module scope */
        (not f.getScope() = u.getEnclosingModule() or ((ImportTimeScope)u.getEnclosingModule()).definesName(f.getName()))
        and
        /* There is a use, but not a definition of this global variable in the function or enclosing scope */
        exists(GlobalVariable v | u.uses(v) |
            not exists(Assign a, Scope defnScope | 
                a.getATarget() = v.getAnAccess() and a.getScope() = defnScope |
                defnScope = f or 
                /* Exclude modules as that case is handled more precisely below. */
                (defnScope = f.getScope().getScope*() and not defnScope instanceof Module)
            )
        )
    )
    and
    not ((ImportTimeScope)u.getEnclosingModule()).definesName(u.getId())
    and
    not globallyDefinedName(u.getId())
    and
    not exists(SsaVariable var | var.getAUse().getNode() = u and not var.maybeUndefined())
    and
    not guarded_against_name_error(u)
    and
    not (u.getEnclosingModule().isPackageInit() and u.getId() = "__path__")
}

pragma [nomagic]
private predicate import_star_defines_name(Module m, string name) {
    exists(ImportStar im | 
        im.getScope() = m and
        exists(ModuleObject imported |
            imported.importedAs(im.getImportedModuleName()) |
            imported.exports(name)
        ) 
    )
}

predicate undefined_use_in_class_or_module(Name u) {
    exists(GlobalVariable v | u.uses(v))
    and
    not exists(Function f | u.getScope().getScope*() = f)
    and
    exists(SsaVariable var | var.getAUse().getNode() = u | var.maybeUndefined())
    and
    not guarded_against_name_error(u)
    and
    not import_star_defines_name(u.getEnclosingModule(), u.getId())
    and
    not (u.getEnclosingModule().isPackageInit() and u.getId() = "__path__")
    and
    not globallyDefinedName(u.getId())
}

from Name u
where (undefined_use_in_class_or_module(u) or undefined_use_in_function(u)) and
      not monkey_patched_builtin(u.getId()) and
      not contains_unknown_import_star(u.getEnclosingModule())
select u, "This use of global variable '" + u.getId()  + "' may be undefined."



