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
 * @name Iterator implementing Iterable
 * @description An 'Iterator' that also implements 'Iterable' by returning itself as its 'Iterator'
 *              does not support multiple traversals. This can lead to unexpected behavior when
 *              it is viewed as an 'Iterable'.
 * @kind problem
 * @problem.severity warning
 */
import java
import IterableClass

/** An `Iterable` that is also its own `Iterator`. */
class IterableIterator extends Iterable {
  IterableIterator() {
    simpleIterator() instanceof ThisAccess
  }
}

/** An `IterableIterator` that never returns any elements. */
class EmptyIterableIterator extends IterableIterator {
  EmptyIterableIterator() {
    exists(Method m |
      m.getDeclaringType().getSourceDeclaration() = this and
      m.getName() = "hasNext" and
      m.getBody().(SingletonBlock).getStmt().(ReturnStmt).getResult().(BooleanLiteral).getBooleanValue() = false
    )
  }
}

from IterableIterator i
where
  // Exclude the empty iterator as that is safe to reuse.
  not i instanceof EmptyIterableIterator
select i, "This Iterable is its own Iterator, but does not guard against multiple iterations."
