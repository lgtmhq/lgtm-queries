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
 * @name __del__ is called explicitly
 * @description The __del__ special method is called by the virtual machine when an object is being finalized. It should not be called explicitly.
 * @kind problem
 * @tags reliability
 *       correctness
 * @problem.severity warning
 * @sub-severity low
 * @precision very-high
 */

import python

class DelCall extends Call {
  DelCall() {
    ((Attribute)this.getFunc()).getName() = "__del__"
  }
  
  predicate isSuperCall() {
    exists(Function f | f = this.getScope() and f.getName() = "__del__" |
      // We pass in `self` as the first argument...
      f.getArg(0).asName().getVariable() = ((Name)this.getArg(0)).getVariable() or
      // ... or the call is of the form `super(Type, self).__del__()`, or the equivalent
      // Python 3: `super().__del__()`.
      exists(Call superCall | superCall = ((Attribute)this.getFunc()).getObject() |
        ((Name)superCall.getFunc()).getId() = "super"
      )
    )
  }
}

from DelCall del
where not del.isSuperCall()
select del, "The __del__ special method is called explicitly."