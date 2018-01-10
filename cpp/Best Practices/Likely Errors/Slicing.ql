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
 * @name Slicing
 * @description Assigning a non-reference instance of a derived type to a variable of the base type slices off all members added by the derived class, and can cause an unexpected state.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @id cpp/slicing
 * @tags reliability
 *       correctness
 *       types
 */
import default

//see http://www.cs.ualberta.ca/~hoover/Courses/201/201-New-Notes/lectures/section/slice.htm
//Does not find anything in rivers (unfortunately)
from AssignExpr e, Class lhsType, Class rhsType
where e.getLValue().getType() = lhsType
  and e.getRValue().getType() = rhsType
  and rhsType.getABaseClass+() = lhsType
  and exists(Declaration m | rhsType.getAMember() = m and
                        not m.(VirtualFunction).isPure()) //add additional checks for concrete members in in-between supertypes
select e, "This assignment expression slices from type $@ to $@",
  rhsType, rhsType.getName(),
  lhsType, lhsType.getName()
