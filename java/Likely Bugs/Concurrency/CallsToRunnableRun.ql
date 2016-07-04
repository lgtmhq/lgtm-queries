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
 * @name Direct call to a run() method
 * @description Directly calling a 'Thread' object's 'run' method does not start a separate thread 
 *              but executes the method within the current thread.
 * @kind problem
 * @problem.severity recommendation
 * @cwe 572
 */
import default

class RunMethod extends Method{
  RunMethod(){
    this.hasName("run") and
    this.hasNoParameters() and
    this.getDeclaringType().getASupertype*().hasQualifiedName("java.lang", "Thread")
  }
}

from MethodAccess m, RunMethod run
where m.getMethod() = run and
      not m.getEnclosingCallable() instanceof RunMethod
select m, "Calling 'Thread.run()' rather than 'Thread.start()' will not spawn a new thread."
