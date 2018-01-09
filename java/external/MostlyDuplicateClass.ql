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
 * @name Mostly duplicate class
 * @description Classes in which most of the methods are duplicated in another class make code more
 *              difficult to understand and introduce a risk of changes being made to only one copy.
 * @kind problem
 * @problem.severity recommendation
 * @precision high
 * @id java/duplicate-class
 * @tags testability
 *       maintainability
 *       useless-code
 *       duplicate-code
 *       statistical
 */
import java
import CodeDuplication

from Class c, string message, Class link
where mostlyDuplicateClass(c, link, message)
  and not fileLevelDuplication(c.getCompilationUnit(), _)
select c, message, link, link.getQualifiedName()
