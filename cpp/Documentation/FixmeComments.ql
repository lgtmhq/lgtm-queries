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
 * @name FIXME comment
 * @description Comments containing 'FIXME' indicate that the code has known bugs.
 * @kind problem
 * @problem.severity warning
 * @precision very-high
 * @tags maintainability
 *       documentation
 *       external/cwe/cwe-546
 */
import default
import Documentation.CaptionedComments

from Comment c, string message
where message = getCommentTextCaptioned(c, "FIXME")
select c, message
