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

/**
 * Holds if `fileAccess` is used in the `fileReadingExpr` to read the represented file.
 */
private predicate fileRead(VarAccess fileAccess, Expr fileReadingExpr) {
  /*
   * `fileAccess` used to construct a class that reads a file.
   */
  exists(ClassInstanceExpr cie |
    cie = fileReadingExpr and
    cie.getArgument(0) = fileAccess |
    cie.getConstructedType().hasQualifiedName("java.io", "RandomAccessFile") or
    cie.getConstructedType().hasQualifiedName("java.io", "FileReader") or
    cie.getConstructedType().hasQualifiedName("java.io", "FileInputStream")
  ) or
  exists(MethodAccess ma, Method filesMethod |
    ma = fileReadingExpr and filesMethod = ma.getMethod() |
    (
      /*
       * Identify all method calls on the `Files` class that imply that we are reading the file
       * represented by the first argument.
       */
      filesMethod.getDeclaringType().hasQualifiedName("java.nio.file", "Files") and
      fileAccess = ma.getArgument(0) and
      (
        filesMethod.hasName("readAllBytes") or
        filesMethod.hasName("readAllLines") or
        filesMethod.hasName("newBufferedReader") or
        filesMethod.hasName("newInputReader") or
        filesMethod.hasName("newByteChannel")
      )
    )
  ) or
  // The `fileAccess` is used in a call which directly or indirectly accesses the file.
  exists(Call call, int parameterPos, VarAccess nestedFileAccess, Expr nestedFileReadingExpr |
    call = fileReadingExpr and
    fileRead(nestedFileAccess, nestedFileReadingExpr) and
    call.getCallee().getParameter(parameterPos) = nestedFileAccess.getVariable() and
    fileAccess = call.getArgument(parameterPos)
  )
}

/**
 * An expression that, directly or indirectly, reads from a file.
 */
class FileReadExpr extends Expr {
  FileReadExpr() {
    fileRead(_,this)
  }

  /**
   * The `VarAccess` representing the file that is read.
   */
  VarAccess getFileVarAccess() {
    fileRead(result, this)
  }
}
