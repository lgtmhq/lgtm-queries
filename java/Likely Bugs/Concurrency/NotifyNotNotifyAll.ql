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
 * @name notify instead of notifyAll
 * @description Calling 'notify' instead of 'notifyAll' may fail to wake up the correct thread and
 *              cannot wake up multiple threads.
 * @kind problem
 * @problem.severity warning
 * @tags reliability
 *       correctness
 *       concurrency
 *       external/cwe/cwe-662
 */

import java

class InvokeInterfaceOrVirtualMethodAccess extends MethodAccess {
  InvokeInterfaceOrVirtualMethodAccess() {
       this.getMethod().getDeclaringType() instanceof Interface
    or not this.hasQualifier() 
    or not this.getQualifier() instanceof SuperAccess
  }
}

from InvokeInterfaceOrVirtualMethodAccess ma, Method m
where ma.getMethod() = m and
      m.hasName("notify") and
      m.hasNoParameters()
select ma, "Using notify rather than notifyAll."
