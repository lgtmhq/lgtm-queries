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
 * @name Throwing pointers
 * @description Exceptions should be objects rather than pointers to objects.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @id cpp/throwing-pointer
 * @tags efficiency
 *       correctness
 *       exceptions
 */

import default

from ThrowExpr throw, NewExpr new, Type t
where new.getParent() = throw
  // Microsoft MFC's CException hierarchy should be thrown (and caught) as pointers
  and t = new.getAllocatedType()
  and not t.getUnderlyingType().(Class).getABaseClass*().hasName("CException")
select throw, "This should throw a " + t.toString() + " rather than a pointer to one."
