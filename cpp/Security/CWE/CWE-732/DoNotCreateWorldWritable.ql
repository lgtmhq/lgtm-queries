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

/**
 * @name File created without restricting permissions
 * @description Creating a file that is world-writable can allow an attacker to write to the file.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @id cpp/world-writable-file-creation
 * @tags security
 *       external/cwe/cwe-732
 */

import cpp
import FilePermissions
import semmle.code.cpp.commons.unix.Constants

predicate worldWritableCreation(FileCreationExpr fc, int mode) {
  mode = localUmask(fc).mask(fc.getMode())
  and
  sets(mode, s_iwoth())
}

predicate setWorldWritable(FunctionCall fc, int mode) {
  exists(string name | fc.getTarget().getName() = name |
    name = "chmod" or
    name = "fchmod" or
    name = "_chmod" or
    name = "_wchmod"
  )
  and
  mode = fc.getArgument(1).getValue().toInt()
  and
  sets(mode, s_iwoth())
}

from Expr fc, int mode, string message
where
  worldWritableCreation(fc, mode) and message = "A file may be created here with mode "+octalFileMode(mode)+", which would make it world-writable."
  or
  setWorldWritable(fc, mode) and message = "This sets a file's permissions to "+octalFileMode(mode)+", which would make it world-writable."
select fc, message
