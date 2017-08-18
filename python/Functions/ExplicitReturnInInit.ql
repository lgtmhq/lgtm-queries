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
 * @name __init__ method returns a value
 * @description Explicitly returning a value from an __init__ method will raise a TypeError.
 * @kind problem
 * @tags reliability
 *       correctness
 * @problem.severity error
 * @sub-severity low
 * @precision very-high
 * @id py/explicit-return-in-init
 */

import python

from Return r
where exists(Function init | init.isInitMethod() and
r.getScope() = init and exists(r.getValue())) and
not r.getValue() instanceof None and
not exists(FunctionObject f | f.getACall() = r.getValue().getAFlowNode() |
    f.neverReturns()
) and
not exists(Attribute meth | meth = ((Call)r.getValue()).getFunc() | meth.getName() = "__init__")
select r, "Explicit return in __init__ method."
