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
 * @name Typo in toString
 * @description A method named 'tostring' may be intended to be named 'toString'.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @id java/tostring-typo
 * @tags maintainability
 *       readability
 *       naming
 */
import java

from Method m
where m.hasName("tostring") and 
      m.hasNoParameters()
select m, "Should this method be called 'toString' rather than 'tostring'?"
