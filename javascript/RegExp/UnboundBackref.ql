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
 * @name Unbound back reference
 * @description Regular expression escape sequences of the form '\n', where 'n' is a positive number
 *              greater than the number of capture groups in the regular expression, are not allowed
 *              by the ECMAScript standard.
 * @kind problem
 * @problem.severity warning
 * @tags reliability
 *       correctness
 *       regular-expressions
 * @precision very-high
 */

import javascript

from RegExpBackRef rebr
where not exists(rebr.getGroup())
select rebr, "Capture group " + rebr.getNumber() + " does not exist."