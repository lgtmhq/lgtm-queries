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
 * @name Wait on condition
 * @description Calling 'wait' on a 'Condition' interface may result in unexpected behavior and is 
 *              probably a typographical error.
 * @kind problem
 * @problem.severity error
 * @cwe 662
 */
import default

class WaitMethod extends Method {
  WaitMethod() {
    this.hasName("wait") and
    this.hasNoParameters() and 
    this.getDeclaringType().hasQualifiedName("java.lang", "Object")
  }
}

class ConditionInterface extends Interface {
  ConditionInterface() {
    this.hasQualifiedName("java.util.concurrent.locks", "Condition")
  }
}

from MethodAccess ma, ConditionInterface condition
where ma.getMethod() instanceof WaitMethod and
      ma.getQualifier().getType().(RefType).hasSupertype*(condition)
select ma, "Waiting for a condition should use Condition.await, not Object.wait."
