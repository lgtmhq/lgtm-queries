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
 * @name Duplicated lines in files
 * @description The number of lines in a file (including code, comment and whitespace lines)
 *              occurring in a block of lines that is duplicated at least once somewhere else.
 * @kind treemap
 * @treemap.warnOn highValues
 * @metricType file
 * @metricAggregate avg sum max
 * @precision high
 * @id js/duplicated-lines-in-files
 * @tags testability
 *       duplicate-code
 */

import external.CodeDuplication

/**
 * Holds if line `l` of file `f` should be excluded from duplicated code detection.
 *
 * Currently, only lines on which an import declaration occurs are excluded.
 */
predicate whitelistedLineForDuplication(File f, int l) {
  exists (ImportDeclaration i | i.getFile() = f and i.getLocation().getStartLine() = l)
}

/**
 * Holds if line `l` of file `f` belongs to a block of lines that is duplicated somewhere else.
 */
predicate dupLine(int l, File f) {
  exists (DuplicateBlock d | d.sourceFile() = f |
    l in [d.sourceStartLine()..d.sourceEndLine()] and
    not whitelistedLineForDuplication(f, l)
  )
}

from File f, int n
where n = count (int l | dupLine(l, f))
select f, n
order by n desc
