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
 * @name Ignored error status of call
 * @description Ignoring an exceptional value that is returned by a method may cause subsequent 
 *              code to fail.
 * @kind problem
 * @problem.severity recommendation
 * @cwe 391
 */
import default

class SpecialMethod extends Method {
  predicate isMethod(string pack, string clss, string name, int numparam) {
    this.hasName(name) and
    this.getNumberOfParameters() = numparam and
    this.getDeclaringType().getASupertype*().getSourceDeclaration().hasQualifiedName(pack, clss)
  }
}

from MethodAccess ma, SpecialMethod m
where ma.getParent() instanceof ExprStmt and
      m = ma.getMethod() and
      (   m.isMethod("java.util", "Queue", "offer", 1)
       or m.isMethod("java.util.concurrent", "BlockingQueue", "offer", 3)
       or m.isMethod("java.util.concurrent.locks", "Condition", "await", 2)
       or m.isMethod("java.util.concurrent.locks", "Condition", "awaitUntil", 1)
       or m.isMethod("java.util.concurrent.locks", "Condition", "awaitNanos", 1)
       or m.isMethod("java.io", "File", "createNewFile", 0) 
       or m.isMethod("java.io", "File", "mkdir", 0)
       or m.isMethod("java.io", "File", "renameTo", 1)
       or m.isMethod("java.io", "File", "setLastModified", 1) 
       or m.isMethod("java.io", "File", "setReadOnly", 0) 
       or m.isMethod("java.io", "File", "setWritable", 1)
       or m.isMethod("java.io", "File", "setWritable", 2)
       or m.isMethod("java.io", "InputStream", "skip", 1) 
       or m.isMethod("java.io", "InputStream", "read", 1)
       or m.isMethod("java.io", "InputStream", "read", 3))
select ma, "Method " + ma.getEnclosingCallable().getName() + " ignores exceptional return value of " 
           + ma.getMethod().getDeclaringType().getName() + "." + ma.getMethod().getName() + "."
