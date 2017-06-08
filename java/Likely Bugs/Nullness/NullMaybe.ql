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
 * @name Dereferenced variable may be null
 * @description Dereferencing a variable whose value may be 'null' may cause a
 *              'NullPointerException'.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @tags reliability
 *       correctness
 *       exceptions
 *       external/cwe/cwe-476
 *       non-local
 */

import java
private import semmle.code.java.dataflow.SSA
private import semmle.code.java.dataflow.Nullness

from VarAccess access, SsaSourceVariable var, string msg, Expr reason
where nullDeref(var, access, msg, reason)
// Exclude definite nulls here, as these are covered by `NullAlways.ql`.
and not alwaysNullDeref(var, access)
select access, "Variable $@ may be null here " + msg + ".",
  var.getVariable(), var.getVariable().getName(), reason, "this"
