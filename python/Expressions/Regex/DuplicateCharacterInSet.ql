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
 * @name Duplication in regular expression character class
 * @description Duplicate characters in a class have no effect and may indicate an error in the regular expression.
 * @kind problem
 * @tags reliability
 *       readability
 * @problem.severity warning
 * @sub-severity low
 * @precision very-high
 * @id py/regex/duplicate-in-character-class
 */

import python
import semmle.python.regex

predicate duplicate_char_in_class(Regex r, string char) {
    exists(int i, int j, int x, int y, int start, int end |
        i != x and j != y and
        start < i and j < end and
        start < x and y  < end and
        r.character(i, j) and char = r.getText().substring(i, j) and
        r.character(x, y) and char = r.getText().substring(x, y) and
        r.charSet(start, end)
    ) and
    /* Exclude � as we use it for any unencodable character */
    char != "�"
}

from Regex r, string char
where duplicate_char_in_class(r, char)
select r, "This regular expression includes duplicate character '" + char + "' in a set of characters."

