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
 * @name Duplicate property
 * @description Listing the same property twice in one object literal is
 *              redundant and may indicate a copy-paste mistake.
 * @kind problem
 * @problem.severity warning
 * @tags maintainability
 */

import Clones

from ObjectExpr oe, int i, int j, Property p, Property q,
     DuplicatePropertyInitDetector dpid
where p = oe.getProperty(i) and q = oe.getProperty(j) and dpid = p.getInit() and
      dpid.same(q.getInit()) and
      i < j and
      // only report the next duplicate
      not exists (int mid | mid in [i+1..j-1] | dpid.same(oe.getProperty(mid).getInit()))
select p, "This property is duplicated $@.", q, "here"