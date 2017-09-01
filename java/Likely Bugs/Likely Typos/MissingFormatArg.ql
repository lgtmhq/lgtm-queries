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
 * @name Missing format argument
 * @description A format call with an insufficient number of arguments causes
 *              an 'IllegalFormatException'.
 * @kind problem
 * @problem.severity error
 * @precision very-high
 * @id java/missing-format-argument
 * @tags correctness
 *       external/cwe/cwe-685
 */
import java
import semmle.code.java.StringFormat

from FormattingCall fmtcall, FormatString fmt, int refs, int args
where
  fmtcall.getAFormatString() = fmt and
  refs = fmt.getMaxFmtSpecIndex() and
  args = fmtcall.getVarargsCount() and
  refs > args
select fmtcall, "This format call refers to " + refs + " argument(s) but only supplies " + args + " argument(s)."
