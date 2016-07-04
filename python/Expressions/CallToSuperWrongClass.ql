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
 * @name First argument to super() is not enclosing class
 * @description Calling super with something other than the enclosing class may cause incorrect object initialization.
 * @kind problem
 * @problem.severity warning
 */

import default

from Call call_to_super, ClassObject cls
where
exists(GlobalVariable gv, Name n, ControlFlowNode cn |
    call_to_super.getFunc() = n and
    n.getVariable() = gv and
    gv.getId() = "super" and
    cn = call_to_super.getArg(0).getAFlowNode() and
    exists(ClassObject other | cn.refersTo(other)) and
    cls.getPyClass() = call_to_super.getScope().getScope() and
    not cn.refersTo(cls)
)
select call_to_super, "First argument to super() should be " + cls.getName() + "."
