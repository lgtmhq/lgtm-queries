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
 * @name Badly bounded write
 * @description Buffer write operations with a length parameter that
 *              does not match the size of the destination buffer may
 *              overflow.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @id cpp/badly-bounded-write
 * @tags reliability
 *       security
 *       external/cwe/cwe-120
 *       external/cwe/cwe-787
 *       external/cwe/cwe-805
 */
import semmle.code.cpp.security.BufferWrite

// see CWE-120UnboundedWrite.ql for a summary of CWE-120 violation cases

from BufferWrite bw, int destSize
where bw.hasExplicitLimit()                     // has an explicit size limit
  and destSize = getBufferSize(bw.getDest(), _)
  and (bw.getExplicitLimit() > destSize)        // but it's larger than the destination
select bw, "This '" + bw.getBWDesc() + "' operation is limited to " + bw.getExplicitLimit() + " bytes but the destination is only " + destSize + " bytes."
