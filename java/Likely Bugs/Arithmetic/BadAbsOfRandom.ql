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
 * @name Incorrect absolute value of random number
 * @description Calling 'Math.abs' to find the absolute value of a randomly generated integer is not
 *              guaranteed to return a non-negative integer.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @id java/abs-of-random
 * @tags reliability
 *       maintainability
 */
import java

from MethodAccess ma, Method abs, Method nextIntOrLong, MethodAccess nma
where ma.getMethod() = abs and
      abs.hasName("abs") and
      abs.getDeclaringType().hasQualifiedName("java.lang","Math") and
      ma.getAnArgument() = nma and
      nma.getMethod() = nextIntOrLong and
      (nextIntOrLong.hasName("nextInt") or nextIntOrLong.hasName("nextLong")) and
      nextIntOrLong.getDeclaringType().hasQualifiedName("java.util","Random") and
      nextIntOrLong.hasNoParameters()
select ma, "Incorrect computation of abs of signed integral random value."
