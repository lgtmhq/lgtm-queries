// Copyright 2016 Semmle Ltd.
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
 * @name Back reference into negative lookahead assertion
 * @description If a back reference refers to a capture group inside a preceding negative lookahead assertion,
 *              then the back reference always matches the empty string, which probably indicates a mistake.
 * @kind problem
 * @problem.severity error
 */

import default

from RegExpNegativeLookahead neg, RegExpGroup grp, RegExpBackRef back
where grp.getParent+() = neg and
      grp = back.getGroup() and
      not back.getParent+() = neg
select back, "This back reference always matches the empty string, since it refers to $@, which is contained in $@.",
       grp, "this capture group",
       neg, "a negative lookahead assertion"
