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
 * @name Missing header guard
 * @description Header files should contain header guards (#defines to prevent the file from being included twice). This prevents errors and inefficiencies caused by repeated inclusion.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @tags efficiency
 *       maintainability
 *       modularity
 */
import default
import semmle.code.cpp.headers.MultipleInclusion

string possibleGuard(HeaderFile hf, string body) {
  exists(Macro m | m.getFile() = hf and m.getBody() = body | result = m.getHead())
}

string extraDetail(HeaderFile hf) {
  exists(string s, PreprocessorDirective ifndef, PreprocessorEndif endif | startsWithIfndef(hf, ifndef, s) and endsWithEndif(hf, endif) and endif.getIf() = ifndef |
    if exists(Macro m | m.getFile() = hf and m.getHead() = s) then
      result = " (#define " + s + " needs to appear immediately after #ifndef " + s + ")."
    else if strictcount(possibleGuard(hf, _)) = 1 then
      result = " (" + possibleGuard(hf, _) + " should appear in the #ifndef rather than " + s + ")."
    else if strictcount(possibleGuard(hf, "")) = 1 then
      result = " (" + possibleGuard(hf, "") + " should appear in the #ifndef rather than " + s + ")."
    else
      result = " (the macro " + s + " is checked for, but is not defined)."
  )
}

from HeaderFile hf, string detail
where not hf instanceof IncludeGuardedHeader
  and (if exists(extraDetail(hf)) then detail = extraDetail(hf) else detail = ".")
  // Exclude files which consist purely of preprocessor directives.
  and not hf.(MetricFile).getNumberOfLinesOfCode() = strictcount(PreprocessorDirective ppd | ppd.getFile() = hf)
  // Exclude files which are always #imported.
  and not forex(Include i | i.getIncludedFile() = hf | i instanceof Import)
  // Exclude files which are only included once.
  and not strictcount(Include i | i.getIncludedFile() = hf) = 1
select hf, "This header file should contain a header guard to prevent multiple inclusion" + detail
