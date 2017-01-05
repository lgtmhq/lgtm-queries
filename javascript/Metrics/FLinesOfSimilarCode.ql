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
 * @name Number of similar lines in files
 * @description The number of lines in a file (including code, comment and whitespace lines)
 *              occurring in a block of lines that is similar to a block of lines seen
 *              somewhere else.
 * @kind treemap
 * @treemap.warnOn highValues
 * @metricType file
 * @metricAggregate avg sum max
 * @tags testability
 */
import external.CodeDuplication

/**
 * Does line l of file f belong to a block of lines that is similar to a block
 * of lines seen somewhere else?
 */
predicate simLine(int l, File f) {
  exists (SimilarBlock d | d.sourceFile() = f |
    l in [d.sourceStartLine()..d.sourceEndLine()]
  )
}

from File f, int n
where n = count (int l | simLine(l, f))
select f, n
order by n desc
