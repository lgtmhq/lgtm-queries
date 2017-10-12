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
 * @name Use of incompletely initialized object
 * @description Accessing 'this' or a property of 'super' in the constructor of a
 *              subclass before calling the super constructor will cause a runtime error.
 * @kind problem
 * @problem.severity error
 * @id js/incomplete-object-initialization
 * @tags correctness
 *       language-features
 * @precision high
 */

import javascript

/**
 * Holds if `e` is an expression of the given `kind` that must be guarded by a
 * call to the super constructor if it appears in the constructor of a class
 * with a superclass.
 */
predicate needsGuard(Expr e, string kind) {
  e instanceof ThisExpr and kind = "this"
  or
  e instanceof SuperPropAccess and kind = "super"
}

/**
 * Holds if `bb` is a basic block that can be reached from the start of `ctor`,
 * which is the constructor of a class that has a superclass, without going through
 * a `super` call.
 */
predicate unguardedBB(BasicBlock bb, Function ctor) {
  exists (ClassDefinition c | exists(c.getSuperClass()) |
    ctor = c.getConstructor().getBody() and
    bb = ctor.getStartBB()
  )
  or
  exists (BasicBlock pred | pred = bb.getAPredecessor() |
    unguardedBB(pred, ctor) and
    not pred.getANode() instanceof SuperCall
  )
}

/**
 * Holds if `nd` is a CFG node that can be reached from the start of `ctor`,
 * which is the constructor of a class that has a superclass, without going through
 * a `super` call.
 */
predicate unguarded(DataFlowNode nd, Function ctor) {
  exists (BasicBlock bb, int i | nd = bb.getNode(i) |
    unguardedBB(bb, ctor) and
    not bb.getNode([0..i-1]) instanceof SuperCall
  )
}

from Expr e, string kind, Function ctor
where needsGuard(e, kind) and unguarded(e, ctor) and
      // don't flag if there is a super call in a nested arrow function
      not exists (SuperCall sc |
        sc.getBinder() = ctor and
        sc.getEnclosingFunction() != ctor
      )
select e, "The super constructor must be called before using '" + kind + "'."