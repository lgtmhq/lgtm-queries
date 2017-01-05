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
 * @name Mismatch in multiple assignment
 * @description Assigning multiple variables without ensuring that you define a
 *              value for each variable causes an exception at runtime.
 * @kind problem
 * @problem.severity error
 * @tags reliability
 *       correctness
 *       types
 */

import python

private  int len(ExprList el) {
	result = count(el.getAnItem())
}

predicate mismatched(Assign a, int lcount, int rcount) {
  exists(ExprList l, ExprList r |
      (((Tuple)a.getATarget()).getElts() = l or ((List)a.getATarget()).getElts() = l)
      and
      (((Tuple)a.getValue()).getElts() = r or ((List)a.getValue()).getElts() = r)
      and
      lcount = len(l) 
      and
      rcount = len(r)
      and 
      lcount != rcount
      and
      not exists(Starred s | l.getAnItem() = s or r.getAnItem() = s))
}

from Assign a, int lcount, int rcount
where mismatched(a, lcount, rcount)
select a, "Different number of variables on either side of assignment; " + lcount.toString() + " versus " + rcount.toString() + "."