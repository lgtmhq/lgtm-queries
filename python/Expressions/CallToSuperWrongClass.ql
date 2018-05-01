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
 * @name First argument to super() is not enclosing class
 * @description Calling super with something other than the enclosing class may cause incorrect object initialization.
 * @kind problem
 * @tags reliability
 *       maintainability
 *       convention
 *       external/cwe/cwe-687
 * @problem.severity error
 * @sub-severity low
 * @precision high
 * @id py/super-not-enclosing-class
 */

import python

from CallNode call_to_super, string name
where
exists(GlobalVariable gv, ControlFlowNode cn |
    call_to_super = theSuperType().getACall() and
    gv.getId() = "super" and
    cn = call_to_super.getArg(0) and
    name = call_to_super.getScope().getScope().(Class).getName() and
    exists(ClassObject other | 
        cn.refersTo(other) and
        not other.getPyClass().getName() = name
    )
)
select call_to_super.getNode(), "First argument to super() should be " + name + "."
