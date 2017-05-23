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
 * @name Non-final method invocation in constructor
 * @description If a constructor calls a method that is overridden in a subclass, the result can be
 *              unpredictable.
 * @kind problem
 * @problem.severity error
 * @precision very-high
 * @tags reliability
 *       correctness
 *       logic
 */
import java

private
predicate writtenInOneCallable(Field f) {
  strictcount(Callable m | m.writes(f)) = 1
}

private
FieldWrite fieldWriteOnlyIn(Callable m, Field f) {
  result.getField() = f and
  m.writes(f) and
  writtenInOneCallable(f)
}

private
FieldRead nonFinalFieldRead(Callable m, Field f) {
  result.getField() = f and
  result.getEnclosingCallable() = m and
  not f.isFinal()
}

private
MethodAccess unqualifiedCallToNonAbstractMethod(Constructor c, Method m) {
  result.getEnclosingCallable() = c and
  (not exists(result.getQualifier()) or
    result.getQualifier().(ThisAccess).getType() = c.getDeclaringType()) and
  m = result.getMethod() and
  not m.isAbstract()
}

from Constructor c, MethodAccess ma, Method m, Method n, Field f, FieldRead fa, Constructor d, FieldWrite fw
where // Method access in a constructor
      // which is an access to the object being initialized, ...
      ma = unqualifiedCallToNonAbstractMethod(c, m) and
      // ... there exists an overriding method in a subtype,
      n.overrides(m) and
      n.getDeclaringType().getASupertype+() = c.getDeclaringType() and
      // ... the method is in a supertype of c,
      m.getDeclaringType() = c.getDeclaringType().getASupertype*() and
      // ... `n` reads a non-final field `f`,
      fa = nonFinalFieldRead(n, f) and
      // ... which is declared in a subtype of `c`,
      f.getDeclaringType().getASupertype+() = c.getDeclaringType() and
      // ... `f` is written only in the subtype constructor, and
      fw = fieldWriteOnlyIn(d, f) and
      // ... the subtype constructor calls (possibly indirectly) the offending super constructor.
      d.callsConstructor+(c) 
select 
ma, "One $@ $@ a $@ that is only $@ in the $@, so it is uninitialized in this $@.",
n, "overriding implementation",
fa, "reads",
f, "subclass field",
fw, "initialized",
d, "subclass constructor",
c, "super constructor"
