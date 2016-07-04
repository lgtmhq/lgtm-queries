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
 * @name Importing value of mutable attribute
 * @description Importing the value of a mutable attribute directly means that changes in global state will not be observed locally.
 * @kind problem
 * @problem.severity error
 */
import python

from ImportMember im, ModuleObject m, AttrNode store_attr, string name
where im.getModule().(ImportExpr).getImportedModuleName() = m.getName() and 
im.getName() = name and
/* Modification must be in a function, so it can occur during lifetime of the import value */
store_attr.getScope() instanceof Function and
/* variable resulting from import must have a long lifetime */
not im.getScope() instanceof Function and
store_attr.isStore() and
store_attr.getObject(name).refersTo(m) and
/* Import not in same module as modification. */
not im.getEnclosingModule() = store_attr.getScope().getEnclosingModule()

select im, "Importing the value of '" + name + "' from $@ means that any change made to $@ will be not be observed locally.",
m, "module " + m.getName(), store_attr, m.getName() + "." + store_attr.getName()
