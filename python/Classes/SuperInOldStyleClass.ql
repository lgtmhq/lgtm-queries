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
 * @name 'super' in old style class
 * @description Using super() to access inherited methods is not supported by old-style classes.
 * @kind problem
 * @problem.severity error
 * @tags portability
 *       correctness
 */

import python

predicate uses_of_super_in_old_style_class(Call s) {
		exists(Function f, ClassObject c | s.getScope() = f and f.getScope() = c.getPyClass() and not c.failedInference() and
		                                   not c.isNewStyle() and ((Name)s.getFunc()).getId() = "super")
}

from Call c
where uses_of_super_in_old_style_class(c)
select c, "super() will not work in old-style classes"