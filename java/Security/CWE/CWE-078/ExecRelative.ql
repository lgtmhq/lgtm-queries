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
 * @name Executing a command with a relative path
 * @description Executing a command with a relative path is vulnerable to
 *              malicious changes in the PATH environment variable.
 * @kind problem
 * @problem.severity error
 * @tags security
 *       external/cwe/cwe-078
 *       external/cwe/cwe-088
 */

import semmle.code.java.Expr
import semmle.code.java.security.RelativePaths
import semmle.code.java.security.ExternalProcess


from ArgumentToExec argument, string command
where
  (
    relativePath(argument, command)
    or arrayStartingWithRelative(argument, command)
  )
  and not shellBuiltin(command)
select argument, "Command with a relative path '" + command + "' is executed."
