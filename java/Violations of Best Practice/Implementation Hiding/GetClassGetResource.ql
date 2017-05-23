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
 * @name Unsafe use of getResource
 * @description Calling 'this.getClass().getResource()' may yield unexpected results if called from a
 *              subclass in another package.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @tags reliability
 *       maintainability
 */
import java

/** Access to a method in `this` object. */
class MethodAccessInThis extends MethodAccess {
  MethodAccessInThis() {
       not this.hasQualifier()
    or this.getQualifier() instanceof ThisAccess
  }
}

from Class c, MethodAccess getResource, MethodAccessInThis getClass
where getResource.getNumArgument() = 1 and
      (   getResource.getMethod().hasName("getResource")
       or getResource.getMethod().hasName("getResourceAsStream")) and
      getResource.getQualifier() = getClass and
      getClass.getNumArgument() = 0 and
      getClass.getMethod().hasName("getClass") and
      getResource.getEnclosingCallable().getDeclaringType() = c and
      c.isPublic()
select getResource, "The idiom getClass().getResource() is unsafe for classes that may be extended."
