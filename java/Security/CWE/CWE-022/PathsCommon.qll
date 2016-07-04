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

import default
import semmle.code.java.controlflow.Dominance

abstract class PathCreation extends Expr {
  abstract Expr getInput();
}

class PathsGet extends PathCreation, MethodAccess {
  PathsGet() {
    exists(Method m | m = this.getMethod() |
      m.getDeclaringType() instanceof TypePaths and
      m.getName() = "get"
    )
  }
  
  Expr getInput() { result = this.getAnArgument() }
  
  Callable getEnclosingCallable() { result = MethodAccess.super.getEnclosingCallable() }
  
  string toString() { result = MethodAccess.super.toString() }
}

class FileSystemGetPath extends PathCreation, MethodAccess {
  FileSystemGetPath() {
    exists(Method m | m = this.getMethod() |
      m.getDeclaringType() instanceof TypeFileSystem and
      m.getName() = "getPath"
    )
  }
  
  Expr getInput() { result = this.getAnArgument() }
  
  Callable getEnclosingCallable() { result = MethodAccess.super.getEnclosingCallable() }
  
  string toString() { result = MethodAccess.super.toString() }
}

class FileCreation extends PathCreation, ClassInstanceExpr {
  FileCreation() {
    this.getConstructedType() instanceof TypeFile
  }
  
  Expr getInput() { 
    result = this.getAnArgument() 
    // Relevant arguments include those that are not a `File`.
    and not result.getType() instanceof TypeFile 
  }
  
  Callable getEnclosingCallable() { result = ClassInstanceExpr.super.getEnclosingCallable() }
  
  string toString() { result = ClassInstanceExpr.super.toString() }
}

class FileWriterCreation extends PathCreation, ClassInstanceExpr {
  FileWriterCreation() {
    this.getConstructedType().getQualifiedName() = "java.io.FileWriter"
  }
  
  Expr getInput() { 
    result = this.getAnArgument() 
    // Relevant arguments are those of type `String`.
    and result.getType() instanceof TypeString 
  }
  
  Callable getEnclosingCallable() { result = ClassInstanceExpr.super.getEnclosingCallable() }
  
  string toString() { result = ClassInstanceExpr.super.toString() }
}

predicate inWeakCheck(Expr e) {
  // None of these are sufficient to guarantee that a string is safe.
  exists(MethodAccess m, Method def | m.getQualifier() = e and m.getMethod() = def |
    def.getName() = "startsWith" or
    def.getName() = "endsWith" or
    def.getName() = "isEmpty" or
    def.getName() = "equals"
  ) or
  // Checking against `null` has no bearing on path traversal.
  exists(EqualityTest b | b.getAnOperand() = e |
    b.getAnOperand() instanceof NullLiteral
  )
}

// Ignore cases where the variable has been checked somehow,
// but allow some particularly obviously bad cases.
predicate guarded(VarAccess e) {
  exists(IfStmt i, Expr c | 
    i.getCondition().getAChildExpr*() = c and 
    c = e.getVariable().getAnAccess() and
    dominates(i, e.getEnclosingStmt()) and
    // Disallow a few obviously bad checks.
    not inWeakCheck(c)
  )
}
