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
 * @name Unmatchable caret in regular expression
 * @description If a caret assertion '^' appears in a regular expression after another term that
 *              cannot match the empty string, then this assertion can never match, so the entire
 *              regular expression cannot match any string.
 * @kind problem
 * @problem.severity error
 * @tags reliability
 *       correctness
 *       regular-expressions
 * @precision very-high
 */

import javascript

from RegExpCaret caret, RegExpTerm t
where t = caret.getPredecessor+() and
      not t.isNullable() and
      // conservative handling of multi-line regular expressions
      not caret.getLiteral().isMultiline()
select caret, "This assertion can never match."