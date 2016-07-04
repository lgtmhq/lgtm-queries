// Copyright 2016 Semmle Ltd.
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
 * @name __init__ method calls overridden method
 * @description Calling a method from __init__ that is overridden by a subclass may result in a partially
 *      initialized instance being observed.
 * @kind problem
 * @problem.severity warning
 */

import python


from ClassObject supercls, string method, Call call,
     FunctionObject overriding, FunctionObject overridden

where
exists(FunctionObject init, SelfAttribute sa |
       supercls.declaredAttribute("__init__") = init and
       call.getScope() = init.getFunction() and call.getFunc() = sa |
       sa.getName() = method and
       overridden = supercls.declaredAttribute(method) and
       overriding.overrides(overridden)
)

select call, "Call to self.$@ in __init__ method, which is overridden by $@.",
  overridden, method,
  overriding, overriding.descriptiveString()




