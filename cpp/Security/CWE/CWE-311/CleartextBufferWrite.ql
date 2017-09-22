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
 * @name Cleartext storage of sensitive information in buffer
 * @description Storing sensitive information in cleartext can expose it
 *              to an attacker.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @tags security
 *       external/cwe/cwe-312
 */

import cpp
import semmle.code.cpp.security.BufferWrite
import semmle.code.cpp.security.TaintTracking
import semmle.code.cpp.security.SensitiveExprs

from BufferWrite w,
     Expr taintedArg, Expr taintSource, string taintCause,
     SensitiveExpr dest
where tainted(taintSource, taintedArg)
  and isUserInput(taintSource, taintCause)
  and w.getASource() = taintedArg
  and dest = w.getDest()
select w, "This write into buffer '" + dest.toString()
        + "' may contain unencrypted data from $@",
       taintSource, "user input (" + taintCause + ")"
