// Copyright 2018 Semmle Ltd.
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
 * @name Use of a potentially dangerous function
 * @description Certain standard library routines are dangerous to call.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @id java/potentially-dangerous-function
 * @tags reliability
 *       security
 *       external/cwe/cwe-676
 */
import java

predicate dangerousMethod(string descriptor) {
  descriptor = "java.lang.Thread.stop"
}

from MethodAccess call, Method target, string descriptor
where
  call.getCallee() = target
  and descriptor = target.getDeclaringType().getQualifiedName() + "." + target.getName()
  and dangerousMethod(descriptor)
select call, "Call to " + descriptor + " is potentially dangerous."
