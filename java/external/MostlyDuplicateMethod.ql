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
 * @name Mostly duplicate method
 * @description Methods in which most of the lines are duplicated in another method make code more
 *              difficult to understand and introduce a risk of changes being made to only one copy.
 * @kind problem
 * @problem.severity recommendation
 * @precision high
 * @tags testability
 *       maintainability
 *       useless-code
 *       duplicate-code
 *       statistical
 */
import java
import CodeDuplication

from Method m, int covered, int total, Method other, int percent
where
  duplicateStatements(m, other, covered, total) and
  covered != total and
  m.getMetrics().getNumberOfLinesOfCode() > 5 and
  covered * 100 / total = percent and
  percent > 80 and
  not duplicateMethod(m, other) and
  not classLevelDuplication(m.getDeclaringType(), other.getDeclaringType()) and
  not fileLevelDuplication(m.getCompilationUnit(), other.getCompilationUnit())
select m, percent + "% of the statements in " + m.getName() + " are duplicated in $@.",
  other, other.getDeclaringType().getName() + "." + other.getStringSignature()
