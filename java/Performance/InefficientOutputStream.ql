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
 * @name Inefficient output stream
 * @description Using the default implementation of 'write(byte[],int,int)'
 *              provided by 'java.io.OutputStream' is very inefficient.
 * @kind problem
 * @problem.severity warning
 * @precision very-high
 * @tags efficiency
 */

import java

class InefficientWriteBytes extends Class {
  InefficientWriteBytes() {
    this.hasQualifiedName("java.io", "OutputStream") or
    this.hasQualifiedName("java.io", "FilterOutputStream")
  }
}


from Class c, Method m
where
  not c.isAbstract()
  and not c instanceof InefficientWriteBytes
  and c.getASupertype() instanceof InefficientWriteBytes
  and c.getAMethod() = m
  and m.getName() = "write"
  and m.getNumberOfParameters() = 1
  and m.getParameterType(0).(PrimitiveType).getName() = "int"
  and exists(Method m2 | c.inherits(m2) |
     m2.getName() = "write" and
     m2.getNumberOfParameters() = 3 and
     m2.getDeclaringType() instanceof InefficientWriteBytes)

  // If that method doesn't call write itself, then we don't have a problem.
  // This is the case is some dummy implementations.
  and exists(MethodAccess ma | ma.getEnclosingCallable() = m | ma.getMethod().getName() = "write")
select c, "This class extends java.io.OutputStream and implements $@, but does not override write(byte[],int,int)", m, m.getName()
