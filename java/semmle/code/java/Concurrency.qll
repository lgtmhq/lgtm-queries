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


import java

/**
 * Whether `e` is synchronized by a local synchronized statement `sync` on the variable `v`.
 */
predicate locallySynchronizedOn(Expr e, SynchronizedStmt sync, Variable v) {
  e.getEnclosingStmt().getParent+() = sync and
  sync.getExpr().(VarAccess).getVariable() = v
}

/**
 * Whether `e` is synchronized by a local synchronized statement on a `this` of type `thisType`, or by a synchronized
 * modifier on the enclosing (non-static) method.
 */
predicate locallySynchronizedOnThis(Expr e, RefType thisType) {
  exists(SynchronizedStmt sync | e.getEnclosingStmt().getParent+() = sync | 
    sync.getExpr().getProperExpr().(ThisAccess).getType().(RefType).getSourceDeclaration() = thisType
  )
  or
  exists(SynchronizedCallable c | c = e.getEnclosingCallable() |
    not c.isStatic() and thisType = c.getDeclaringType()
  )
}

/**
 * Whether `e` is synchronized by a `synchronized` modifier on the enclosing (static) method.
 */
predicate locallySynchronizedOnClass(Expr e, RefType classType) {
  exists(SynchronizedCallable c | c = e.getEnclosingCallable() |
    c.isStatic() and classType = c.getDeclaringType()
  )
}

/**
 * A callable that is synchronized on its enclosing instance, either by a `synchronized` modifier, or
 * by having a body which is precisely `synchronized(this) { ... }`.
 */
class SynchronizedCallable extends Callable {
  SynchronizedCallable() {
    this.isSynchronized()
    or
    // The body is just `synchronized(this) { ... }`.
    exists(SynchronizedStmt s | this.getBody().(SingletonBlock).getStmt() = s |
      s.getExpr().(ThisAccess).getType() = this.getDeclaringType()
    )
  }
}
