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
 * @name TODO comment
 * @description A comment that contains 'TODO' or similar keywords may indicate code that is incomplete or
 *              broken, or it may highlight an ambiguity in the software's specification.
 * @kind problem
 * @problem.severity recommendation
 * @id js/todo-comment
 * @tags maintainability
 *       external/cwe/cwe-546
 * @precision very-high
 */

import javascript

from Comment c
where c.getText().regexpMatch("(?s).*FIXME.*|.*TODO.*|.*(?<!=)\\s*XXX.*")
select c, "TODO comments should be addressed."