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
 * @name Interface cannot be implemented
 * @description An interface method that is incompatible with a protected method on
 *              'java.lang.Object' means that the interface cannot be implemented.
 * @kind problem
 * @problem.severity warning
 * @tags maintainability
 *       useless-code
 */

import java

Method protectedObjectMethod(string signature) {
  result.getSignature() = signature and
  result.isProtected() and
  result.getDeclaringType() instanceof TypeObject
}

from Method method, Method objMethod, Interface impossible
where method.getDeclaringType() = impossible
  and objMethod = protectedObjectMethod(method.getSignature())
  and not hasSubtype*(objMethod.getReturnType(), method.getReturnType())
select method,
  "This method's return type conflicts with Object." + method.getName() + " so $@ can never be implemented.",
  impossible,
  impossible.getName()
