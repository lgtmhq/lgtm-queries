// Copyright 2018 Semmle Ltd.
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
import semmle.code.java.dataflow.Guards

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

  override Expr getInput() { result = this.getAnArgument() }
}

class FileSystemGetPath extends PathCreation, MethodAccess {
  FileSystemGetPath() {
    exists(Method m | m = this.getMethod() |
      m.getDeclaringType() instanceof TypeFileSystem and
      m.getName() = "getPath"
    )
  }

  override Expr getInput() { result = this.getAnArgument() }
}

class FileCreation extends PathCreation, ClassInstanceExpr {
  FileCreation() {
    this.getConstructedType() instanceof TypeFile
  }

  override Expr getInput() {
    result = this.getAnArgument() and
    // Relevant arguments include those that are not a `File`.
    not result.getType() instanceof TypeFile
  }
}

class FileWriterCreation extends PathCreation, ClassInstanceExpr {
  FileWriterCreation() {
    this.getConstructedType().getQualifiedName() = "java.io.FileWriter"
  }

  override Expr getInput() {
    result = this.getAnArgument() and
    // Relevant arguments are those of type `String`.
    result.getType() instanceof TypeString
  }
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
  exists(PathCreation p | e = p.getInput()) and
  exists(ConditionBlock cb, Expr c |
    cb.getCondition().getAChildExpr*() = c and
    c = e.getVariable().getAnAccess() and
    cb.controls(e.getBasicBlock(), true) and
    // Disallow a few obviously bad checks.
    not inWeakCheck(c)
  )
}
