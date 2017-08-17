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
 * @name Import shadowed by loop variable
 * @description A loop variable shadows an import.
 * @kind problem
 * @tags maintainability
 * @problem.severity recommendation
 * @sub-severity low
 * @precision very-high
 * @id py/import-shadowed-loop-variable
 */

import python

predicate shadowsImport(Variable l) {
    exists(Import i, Name shadow | shadow = i.getAName().getAsname() and shadow.getId() = l.getId() and i.getScope() = l.getScope().getScope*())
}


from Variable l, Name defn
where shadowsImport(l) and defn.defines(l) and exists(For for | defn = for.getTarget())
select defn, "Loop variable '" + l.getId() + "' shadows an import"
