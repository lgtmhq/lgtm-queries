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

import java
import semmle.code.java.comparison.Comparison

/**
 * An `equals` method that implies the superclass `equals` method is a "finer" equality check. 
 * 
 * Importantly, in this case an inherited hash code is still valid, since
 * 
 *     subclass equals holds => superclass equals holds => hash codes match
 */
class RefiningEquals extends EqualsMethod {
  RefiningEquals() {
    // For each return statement `ret` in this method, ...
    forall(ReturnStmt ret | ret.getEnclosingCallable() = this |
      // ... there is a `super` access that ...
      exists(MethodAccess sup, SuperAccess qual | 
        // ... is of the form `super.something`, but not `A.super.something` ...
        qual = sup.getQualifier() and not exists(qual.getQualifier())
        // ... calls `super.equals` ...
        and sup.getCallee() instanceof EqualsMethod 
        // ... on the (only) parameter of this method ...
        and sup.getArgument(0).(VarAccess).getVariable() = this.getAParameter()
        // ... and its result is implied by the result of `ret`.
        and exprImplies(ret.getResult(), true, sup, true)
      )
    )
  }
}
