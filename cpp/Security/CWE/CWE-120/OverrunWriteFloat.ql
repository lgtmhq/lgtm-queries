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
 * @name Potentially overrunning write with float to string conversion
 * @description Buffer write operations that do not control the length
 *              of data written may overflow when floating point inputs
 *              take extreme values.
 * @kind problem
 * @problem.severity error
 * @precision medium
 * @id cpp/overrunning-write-with-float
 * @tags reliability
 *       security
 *       external/cwe/cwe-120
 *       external/cwe/cwe-787
 *       external/cwe/cwe-805
 */
import semmle.code.cpp.security.BufferWrite

// see CWE-120UnboundedWrite.ql for a summary of CWE-120 violation cases

from BufferWrite bw, int destSize
where (not bw.hasExplicitLimit())                // has no explicit size limit
  and destSize = getBufferSize(bw.getDest(), _)
  and (bw.getMaxData() > destSize)               // and we can deduce that too much data may be copied
  and (bw.getMaxDataLimited() <= destSize)       // but it would fit without long '%f' conversions
select bw, "This '" + bw.getBWDesc() + "' operation may require " + bw.getMaxData() + " bytes because of float conversions, but the target is only " + destSize + " bytes."
