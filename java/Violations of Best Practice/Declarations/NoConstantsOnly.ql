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
 * @name Constant interface anti-pattern
 * @description Implementing an interface (or extending an abstract class)
 *              only to put a number of constant definitions into scope is considered bad practice.
 * @kind problem
 * @problem.severity recommendation
 * @tags maintainability
 *       modularity
 */

import semmle.code.java.Member

class ConstantField extends Field {
  ConstantField() {
    this.isStatic() and this.isFinal()
  }
}

pragma[noinline]
predicate typeWithConstantField(RefType t) {
  exists(ConstantField f | f.getDeclaringType() = t)
}

class ConstantRefType extends RefType {
  ConstantRefType() {
    fromSource() and
    (   this instanceof Interface
     or this instanceof Class and this.isAbstract()) and
    typeWithConstantField(this) and
    forall(Member m | m.getDeclaringType() = this |
      m.(Constructor).isDefaultConstructor() or
      m instanceof StaticInitializer or
      m instanceof ConstantField
    )
  }

  string getKind() {
    result = "interface" and this instanceof Interface or
    result = "class" and this instanceof Class
  }
}

from ConstantRefType t, RefType sub
where sub.fromSource()
  and sub.getASupertype() = t
  and not sub instanceof ConstantRefType
  and sub = sub.getSourceDeclaration()
select sub, "Type " + sub.getName() + " implements constant " + t.getKind() + " $@.",
       t, t.getName()
