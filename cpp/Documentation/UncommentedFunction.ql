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
 * @name Poorly documented large function
 * @description Large functions that have no or almost no comments are likely to be too complex to understand and maintain. The larger a function is, the more problematic the lack of comments.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @id cpp/poorly-documented-function
 * @tags maintainability
 *       documentation
 *       statistical
 */
import default

from MetricFunction f, int n
where n = f.getNumberOfLines() and n > 100 and
      f.getCommentRatio() <= 0.02 and
      not f.isMultiplyDefined()
select f, "Poorly documented function: fewer than 2% comments for a function of " + n.toString() + " lines."
