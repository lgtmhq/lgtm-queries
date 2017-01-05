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
 * @name Non-iterator used in for loop
 * @description Using a non-iterable as the object in a 'for' loop causes a TypeError.
 * @kind problem
 * @problem.severity warning
 * @tags reliability
 *       correctness
 *       types
 */

import python

from For loop, ControlFlowNode iter, ClassObject t, ControlFlowNode origin
where loop.getIter().getAFlowNode() = iter and
iter.refersTo(_, t, origin) and 
not t.isIterable() and not t.failedInference() and
not t = theNoneType() and
not t.isDescriptorType()

select loop, "$@ of class '$@' may be used in for-loop.", origin, "Non-iterator", t, t.getName()
