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
 * @name Use of default toString()
 * @description Calling the default implementation of 'toString' returns a value that is unlikely to
 *              be what you expect.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @id java/call-to-object-tostring
 * @tags reliability
 *       maintainability
 */
import java

predicate printMethod(Method m) {
  (m.hasName("print") or m.hasName("println"))
  and m.getNumberOfParameters() = 1
  and exists(RefType t | t = m.getDeclaringType() |
    t.hasName("PrintWriter") or t.hasName("PrintStream")
  )
}

predicate implicitToStringCall(Expr e) {
  exists(AddExpr add | 
    add.getAnOperand() = e and
    add.getType() instanceof TypeString
  )
  or exists(MethodAccess ma |
    ma.getAnArgument() = e and
    printMethod(ma.getMethod())
  )
}

predicate explicitToStringCall(Expr e) {
  exists(MethodAccess ma, Method toString | toString = ma.getMethod() | 
    e = ma.getQualifier() and
    toString.getName() = "toString" and
    toString.getNumberOfParameters() = 0 and
    not toString.isStatic()
  )
}

predicate directlyDeclaresToString(Class c) {
  exists(Method m | m.getDeclaringType() = c |
    m.getName() = "toString" and
    m.getNumberOfParameters() = 0
  )
}

predicate inheritsObjectToString(Class t) {
  not directlyDeclaresToString(t.getSourceDeclaration()) and
  (
    t.getASupertype().hasQualifiedName("java.lang", "Object")
    or
    (
      not t.getASupertype().hasQualifiedName("java.lang", "Object")
      and inheritsObjectToString(t.getASupertype())
    )
  )
}

Class getAnImplementation(RefType parent) {
  result = parent.getASubtype*() and
  not result.isAbstract()
}

predicate bad(RefType t) {
  forex(Class sub | sub = getAnImplementation(t) | inheritsObjectToString(sub))
  and not t instanceof Array 
  and not t instanceof GenericType
  and not t instanceof BoundedType
}

predicate logContext(Expr e) {
  exists(ClassInstanceExpr cie |
    cie.getConstructor().getDeclaringType().getASupertype*().hasName("Throwable") |
    e = cie.getAnArgument()
  ) or
  exists(MethodAccess ma | 
    ma.getMethod().getName().toLowerCase().matches("%log%") or
    ma.getMethod().getDeclaringType().getName().toLowerCase().matches("%log%") | 
    e = ma.getAnArgument()
  )
}

from Expr e, RefType sourceType
where (implicitToStringCall(e) or explicitToStringCall(e))
  and sourceType = e.getType().(RefType).getSourceDeclaration()
  and bad(sourceType)
  and not sourceType.isAbstract()
  and sourceType.fromSource()
  and not exists(Expr log | logContext(log) | e = log.getAChildExpr*())
  and sourceType != e.getEnclosingCallable().getDeclaringType()
select e, "Default toString(): " + e.getType().getName() +
  " inherits toString() from Object, and so is not suitable for printing."
