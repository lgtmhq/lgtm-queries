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
 * @name Duplicate method
 * @description Duplicated methods make code more difficult to understand and introduce a risk of
 *              changes being made to only one copy.
 * @kind problem
 * @problem.severity recommendation
 * @precision high
 * @id java/duplicate-method
 * @tags testability
 *       maintainability
 *       useless-code
 *       duplicate-code
 *       statistical
 */
import java
import CodeDuplication

predicate relevant(Method m) {
  m.getNumberOfLinesOfCode() > 5 and not m.getName().matches("get%")
  or m.getNumberOfLinesOfCode() > 10
}

from Method m, Method other
where duplicateMethod(m, other)
  and relevant(m)
  and not fileLevelDuplication(m.getCompilationUnit(), other.getCompilationUnit())
  and not classLevelDuplication(m.getDeclaringType(), other.getDeclaringType())
select m, "Method " + m.getName() + " is duplicated in $@.",
  other, other.getDeclaringType().getQualifiedName()
