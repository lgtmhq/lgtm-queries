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
 * @name Backspace escape in regular expression
 * @description Using '\b' to escape the backspace character in a regular expression is confusing
 *              since it could be mistaken for a word boundary assertion.
 * @kind problem
 * @problem.severity warning
 * @tags maintainability
 */

import python
import semmle.python.regex

from Regex r, int offset
where r.escapingChar(offset) and r.getChar(offset+1) = "b" and 
exists(int start, int end |
    start < offset and end > offset |
    r.charSet(start, end)
)
select r, "Backspace escape in regular expression at offset " + offset + "."