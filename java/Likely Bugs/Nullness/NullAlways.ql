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
 * @name Dereferenced variable is always null
 * @description Dereferencing a variable whose value is 'null' causes a 'NullPointerException'.
 * @kind problem
 * @problem.severity error
 * @tags reliability
 *       correctness
 *       exceptions
 *       external/cwe/cwe-476
 */

import java
private import semmle.code.java.dataflow.Nullness

from VarAccess access, LocalScopeVariable var
where alwaysNullDeref(var, access)
select access, "Variable $@ is always null here.", var, var.getName()
