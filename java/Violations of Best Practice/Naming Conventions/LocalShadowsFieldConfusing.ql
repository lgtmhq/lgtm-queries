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
 * @name Possible confusion of local and field
 * @description A method in which a variable is declared with the same name as a field is difficult
 *              to understand.
 * @kind problem
 * @problem.severity warning
 * @precision very-high
 * @tags maintainability
 *       readability
 */
import java
import Shadowing

from LocalVariableDecl d, Class c, Field f, Callable callable, string callableType, string message
where shadows(d, c, f, callable) and
      not assignmentToShadowingLocal(d, f) and
      not assignmentFromShadowingLocal(d, f) and
      (if callable instanceof Constructor
       then callableType = ""
       else callableType = "method ") and
      (
        (confusingAccess(d, f) and 
         message = "Confusing name: " + callableType +
                   "$@ also refers to field $@ (without qualifying it with 'this').")
        or
        (thisAccess(d, f) and not confusingAccess(d, f) and 
         message = "Potentially confusing name: " + callableType +
                   "$@ also refers to field $@ (as this." + f.getName() + ").")
      )
select d, message, callable, callable.getName(), f, f.getName()
