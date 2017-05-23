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
 * @name Inconsistent synchronization of getter and setter
 * @description If a class has a synchronized 'set' method, and a similarly-named 'get' method is
 *              not also synchronized, calls to the 'get' method may not return a consistent state
 *              for the object.
 * @kind problem
 * @problem.severity error
 * @precision very-high
 * @tags reliability
 *       correctness
 *       concurrency
 *       language-features
 *       external/cwe/cwe-413
 *       external/cwe/cwe-662
 */
import java

/**
 * Holds if this method is synchronized by a `synchronized(Foo.class){...}` block
 * (for static methods) or a `synchronized(this){...}` block (for instance methods).
 */
predicate isSynchronizedByBlock(Method m) {
  exists(SynchronizedStmt sync, Expr on |
    sync = m.getBody().getAChild*() and on = sync.getExpr().getProperExpr() |
    if m.isStatic() then
      on.(TypeLiteral).getTypeName().getType() = m.getDeclaringType()
    else
      on.(ThisAccess).getType().(RefType).getSourceDeclaration() = m.getDeclaringType()
  )
}

/**
 * Holds if `get` is a getter method for a volatile field that `set` writes to.
 *
 * In this case, even if `set` is synchronized and `get` is not, `get` will never see stale
 * values for the field, so synchronization is optional.
 */
predicate bothAccessVolatileField(Method set, Method get) {
  exists (Field f | f.isVolatile() |
    f = get.(GetterMethod).getField() and
    f.getAnAccess().(FieldWrite).getEnclosingCallable() = set
  )
}

from Method set, Method get
where set.getDeclaringType() = get.getDeclaringType() and
      set.getName().matches("set%") and
      get.getName() = "get"+set.getName().substring(3,set.getName().length()) and
      set.isSynchronized() and
      not (get.isSynchronized() or isSynchronizedByBlock(get)) and
      not bothAccessVolatileField(set, get) and
      set.fromSource()
select get, "This get method is unsynchronized, but the corresponding $@ is synchronized.",
  set, "set method"
