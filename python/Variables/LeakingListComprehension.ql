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
 * @name List comprehension variable used in enclosing scope
 * @description Using the iteration variable of a list comprehension in the enclosing scope will result in different behavior between Python 2 and 3 and is confusing.
 * @kind problem
 * @problem.severity error
 * @tags portability
 *       correctness
 */

import python

SsaVariable py2_list_comp_variable(ListComp l) {
    result.getDefinition().getNode() = l.getAGenerator().getTarget()
}


from ListComp l, SsaVariable v, Name use
where
  v = py2_list_comp_variable(l) and
  exists(SsaVariable uv |
      uv.getAUse().getNode() = use |
      uv.getAnUltimateDefinition() = v
  ) and
  not l.contains(use)
  and
  not use.deletes(_)
select use, v.getId() + " may have a different value in Python 3, as the $@ will not be in scope.", v, "list comprehension variable" 






