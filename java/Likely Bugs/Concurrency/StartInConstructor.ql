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
 * @name Start of thread in constructor
 * @description Starting a thread within a constructor may cause the thread to start before
 *              any subclass constructor has completed its initialization, causing unexpected
 *              results.
 * @kind problem
 * @problem.severity warning
 * @tags reliability
 *       correctness
 *       concurrency
 */
import java

/**
 * Whether this type is either `final` or
 * `private` and without subtypes.
 */
private predicate cannotBeExtended(RefType t) {
  t.isFinal()
  or
  // If the class is private, all possible subclasses are known.
  t.isPrivate() and not exists(RefType sub | sub != t | sub.getAnAncestor() = t)
}

from MethodAccess m, Constructor c, Class clazz
where m.getMethod().getDeclaringType().hasQualifiedName("java.lang", "Thread") and 
      m.getMethod().getName() = "start" and 
      m.getEnclosingCallable() = c and 
      c.getDeclaringType() = clazz and
      not cannotBeExtended(clazz)
select m, "Class $@ starts a thread in its constructor.", clazz, clazz.getName()
