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
 * @name Creates empty ZIP file entry
 * @description Omitting a call to 'ZipOutputStream.write' when writing a ZIP file to an output
 *              stream means that an empty ZIP file entry is written.
 * @kind problem
 * @problem.severity warning
 */
import default

/** A class that is a descendant of `java.util.zip.ZipOutputStream`. */
class ZipOutputStream extends Class {
  ZipOutputStream() {
    exists(Class zip | zip.hasQualifiedName("java.util.zip", "ZipOutputStream") |
      this.hasSupertype*(zip)
    )
  }
 
  Method putNextEntry() {
    (   result.getDeclaringType() = this
     or this.inherits(result)) and
    result.getName() = "putNextEntry" and 
    result.getNumberOfParameters() = 1 and
    result.getAParamType().(Class).hasQualifiedName("java.util.zip", "ZipEntry")
  }
 
  Method closeEntry() {
    (   result.getDeclaringType() = this
     or this.inherits(result)) and
    result.getName() = "closeEntry" and 
    result.getNumberOfParameters() = 0
  }
}
  
from ZipOutputStream jos, MethodAccess putNextEntry, MethodAccess closeEntry,
     Stmt putNextStmt, Stmt closeStmt
where putNextEntry.getMethod() = jos.putNextEntry() and
     closeEntry.getMethod() = jos.closeEntry() and
     putNextStmt = putNextEntry.getEnclosingStmt() and
     closeStmt = closeEntry.getEnclosingStmt() and
     closeStmt = putNextStmt.getASuccessor() and
     not exists(Stmt other | other.getASuccessor() = closeStmt |
       other != putNextStmt
     )
select closeEntry, "Empty ZIP file entry created."
