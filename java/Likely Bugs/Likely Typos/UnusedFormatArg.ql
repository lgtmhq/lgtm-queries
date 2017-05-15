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
 * @name Unused format argument
 * @description A format call with a format string that refers to fewer
 *              arguments than the number of supplied arguments will silently
 *              ignore the additional arguments.
 * @kind problem
 * @problem.severity warning
 * @tags maintainability
 *       useless-code
 *       external/cwe/cwe-685
 */
import java
import semmle.code.java.StringFormat

int getNumberOfReferencedIndices(FormattingCall fmtcall) {
  exists(int maxref, int skippedrefs |
    maxref = max(FormatString fmt | fmtcall.getAFormatString() = fmt | fmt.getMaxFmtSpecIndex()) and
    skippedrefs = count(int i |
      forex(FormatString fmt | fmtcall.getAFormatString() = fmt | i = fmt.getASkippedFmtSpecIndex())
    ) and
    result = maxref - skippedrefs
  )
}

from FormattingCall fmtcall, int refs, int args
where
  refs = getNumberOfReferencedIndices(fmtcall) and
  args = fmtcall.getVarargsCount() and
  refs < args
select fmtcall, "This format call refers to " + refs + " argument(s) but supplies " + args + " argument(s)."
