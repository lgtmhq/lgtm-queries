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
 * @name Uncontrolled data used in path expression
 * @description Accessing paths influenced by users can allow an attacker to access unexpected resources.
 * @kind problem
 * @problem.severity error
 * @cwe 022 023 036 073
 */
import default
import semmle.code.java.security.DataFlow
import PathsCommon

from RemoteUserInput u, PathCreation p, Expr e
where 
  e = p.getInput()
  and u.flowsTo(e)
  and not guarded(e)
select p, "$@ flows to here and is used in a path.", u, "User-provided value"
