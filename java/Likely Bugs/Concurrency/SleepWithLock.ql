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
 * @name Sleep with lock held
 * @description Calling 'Thread.sleep' with a lock held may lead to very poor
 *              performance or even deadlock.
 * @kind problem
 * @problem.severity error
 * @precision medium
 * @tags reliability
 *       correctness
 *       concurrency
 *       external/cwe/cwe-833
 */
import java

from MethodAccess ma, Method sleep
where ma.getMethod() = sleep and
      sleep.hasName("sleep") and
      sleep.getDeclaringType().hasQualifiedName("java.lang", "Thread") and
      (   ma.getEnclosingStmt().getParent*() instanceof SynchronizedStmt
       or ma.getEnclosingCallable().isSynchronized())
select ma, "sleep() with lock held."
