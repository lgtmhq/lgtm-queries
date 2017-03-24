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
 * @name Asserting a tuple
 * @description Using an assert statement to test a tuple provides no validity checking.
 * @kind problem
 * @tags reliability
 *       maintainability
 * @problem.severity error
 * @sub-severity low
 * @precision very-high
 */

import python

from Assert a, string b, string non
where a.getTest() instanceof Tuple and
			(if exists(((Tuple)a.getTest()).getAnElt()) then
			    (b = "True" and non = "non-")
       else
          (b = "False" and non = "")
      )
select a, "Assertion of " + non + "empty tuple is always " + b + "."

