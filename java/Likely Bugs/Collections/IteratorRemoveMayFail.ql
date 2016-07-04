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
 * @name Call to Iterator.remove may fail
 * @description Attempting to invoke 'Iterator.remove' on an iterator over a collection that does not
 *              support element removal causes a runtime exception.
 * @kind problem
 * @problem.severity warning
 */

import default

class SpecialCollectionCreation extends MethodAccess {
  SpecialCollectionCreation() {
    exists (Method m, RefType rt | m = this.(MethodAccess).getCallee() and rt = m.getDeclaringType() |
      (rt.hasQualifiedName("java.util", "Arrays") and m.hasName("asList")) or
      (rt.hasQualifiedName("java.util", "Collections") and m.getName().regexpMatch("singleton.*|unmodifiable.*"))
    )
  }
}

predicate containsSpecialCollection(Expr e, SpecialCollectionCreation origin) {
  e = origin or
  exists(Variable v |
    containsSpecialCollection(v.getAnAssignedValue(), origin) and
    e = v.getAnAccess()
  ) or
  exists(Call c, int i |
    containsSpecialCollection(c.getArgument(i), origin) and
    e = c.getCallee().getParameter(i).getAnAccess()
  ) or
  exists(Call c, ReturnStmt r | e = c |
    r.getEnclosingCallable() = c.getCallee() and
    containsSpecialCollection(r.getResult(), origin)
  )
}

predicate iterOfSpecialCollection(Expr e, SpecialCollectionCreation origin) {
  exists(MethodAccess ma | ma = e |
    containsSpecialCollection(ma.getQualifier(), origin) and
    ma.getCallee().hasName("iterator")
  ) or
  exists(Variable v |
    iterOfSpecialCollection(v.getAnAssignedValue(), origin) and
    e = v.getAnAccess()
  ) or
  exists(Call c, int i |
    iterOfSpecialCollection(c.getArgument(i), origin) and
    e = c.getCallee().getParameter(i).getAnAccess()
  ) or
  exists(Call c, ReturnStmt r | e = c |
    r.getEnclosingCallable() = c.getCallee() and
    iterOfSpecialCollection(r.getResult(), origin)
  )
}

from MethodAccess remove, SpecialCollectionCreation scc
where remove.getCallee().hasName("remove") and
      iterOfSpecialCollection(remove.getQualifier(), scc)
select remove,
  "This call may fail when iterating over the collection created $@, since it does not support element removal.",
  scc, "here"
