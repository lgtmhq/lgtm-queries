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
 * @name Futile synchronization on field
 * @description Synchronizing on a field and updating that field while the lock is held is unlikely
 *              to provide the desired thread safety.
 * @kind problem
 * @problem.severity error
 * @precision medium
 * @tags reliability
 *       correctness
 *       concurrency
 *       language-features
 *       external/cwe/cwe-662
 */
import java

private
Field synchField(SynchronizedStmt s) {
  result = s.getExpr().(VarAccess).getVariable()
}

private
Field assignmentToField(Assignment a) {
  result = a.getDest().(VarAccess).getVariable()
}

from SynchronizedStmt s, Field f, Assignment a
where synchField(s) = f and
      assignmentToField(a) = f and
      a.getEnclosingStmt().getParent*() = s
select a, "Synchronization on field $@ in futile attempt to guard that field.",
       f, f.getDeclaringType().getName() + "." + f.getName()
