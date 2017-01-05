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
 * @name Explicit thread priority
 * @description Setting thread priorities to control interactions between threads is not portable,
 *              and may not have the desired effect.
 * @kind problem
 * @problem.severity warning
 * @tags portability
 *       correctness
 *       concurrency
 */
import java

class PriorityMethod extends Method {
  PriorityMethod() {
    (this.getName() = "setPriority" or this.getName() = "getPriority") and
    this.getDeclaringType().hasQualifiedName("java.lang","Thread")
  }
}

class PriorityMethodAccess extends MethodAccess {
  PriorityMethodAccess() {
    this.getMethod() instanceof PriorityMethod
  }
}

from PriorityMethodAccess ma
where ma.getCompilationUnit().fromSource()
select ma, "Avoid using thread priorities. The effect is unpredictable and not portable."
