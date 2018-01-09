// Copyright 2018 Semmle Ltd.
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
 * @name Lines of commented-out code in files
 * @description The number of lines of commented-out code in a file.
 * @kind treemap
 * @treemap.warnOn highValues
 * @metricType file
 * @metricAggregate avg sum max
 * @precision high
 * @id java/lines-of-commented-out-code-in-files
 * @tags maintainability
 *       documentation
 */
 
import Violations_of_Best_Practice.Comments.CommentedCode

from File f, int n
where n = sum(CommentedOutCode comment | comment.getFile() = f | comment.getCodeLines())
select f, n
order by n desc
