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
 * @name Confusing octal literal
 * @description Octal literal with a leading 0 is easily misread as a decimal value
 * @kind problem
 * @tags changeability
 *       readability
 * @problem.severity recommendation
 * @sub-severity low
 * @precision high
 */

import python

predicate is_old_octal(IntegerLiteral i) {
    exists(string text |
        text = i.getText() |
        text.charAt(0) = "0" and
        not text = "00" and
        exists(text.charAt(1).toInt()) and
        /* Do not flag file permission masks */
        exists(int len | len = text.length() |
            len != 4 and
            len != 5 and
            len != 7
        )
    )
}

from IntegerLiteral i
where is_old_octal(i)
select i, "Confusing octal literal, use 0o" + i.getText().suffix(1) + " instead."
