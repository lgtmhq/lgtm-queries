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
 * @name Implicit conversion from array to string
 * @description Directly printing an array, without first converting the array to a string,
 *              produces unreadable results.
 * @kind problem
 * @problem.severity recommendation
 * @precision very-high
 * @id java/print-array
 * @tags maintainability
 */
import java
import semmle.code.java.StringFormat

/**
 * Holds if `e` is an argument of `Arrays.toString(..)`.
 */
predicate arraysToStringArgument(Expr e) {
  exists(MethodAccess ma, Method m |
    ma.getAnArgument() = e and
    ma.getMethod() = m and
    m.getDeclaringType().hasQualifiedName("java.util", "Arrays") and
    m.hasName("toString")
  )
}
from Expr arr
where
  arr.getType() instanceof Array and
  implicitToStringCall(arr)
  or
  arr.getType().(Array).getComponentType() instanceof Array and
  arraysToStringArgument(arr)
select arr, "Implicit conversion from Array to String."
