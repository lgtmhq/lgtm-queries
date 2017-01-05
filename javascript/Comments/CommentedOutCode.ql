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
 * @name Commented-out code
 * @description Comments that contain commented-out code should be avoided.
 * @kind problem
 * @problem.severity recommendation
 * @tags maintainability
 */

import javascript
import CommentedOut

/**
 * Does this comment look like an annotation for the [Flow](https://flowtype.org/)
 * type checker?
 */
predicate isFlowAnnotation(SlashStarComment c) {
  c.getText().regexpMatch("^(?s)\\s*(: |::|flow-include ).*")
}

from CommentedOutCode c
where not isFlowAnnotation(c)
select c, "This comment appears to contain commented-out code."