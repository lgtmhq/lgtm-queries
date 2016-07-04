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
 * @name Busy wait
 * @description Calling 'Thread.sleep' to control thread interaction is
 *              less effective than waiting for a notification and may also 
 *              result in race conditions. Merely synchronizing over shared 
 *              variables in a loop to control thread interaction 
 *              may waste system resources and cause performance problems.
 * @kind problem
 * @problem.severity warning
 */
import default

class ReachFromStmt extends Stmt {
  ReachFromStmt() {
    exists(Method m | m.getBody() = this) or
    exists(WhileStmt w | w.getStmt() = this)
  }
}

class SleepMethod extends Method {
  SleepMethod() {
    this.getName() = "sleep" and
    this.getDeclaringType().hasQualifiedName("java.lang","Thread")
  }
}

class SleepMethodAccess extends MethodAccess {
  SleepMethodAccess() {
    this.getMethod() instanceof SleepMethod
  }
}

class WaitMethod extends Method {
  WaitMethod() {
    this.getName() = "wait" and
    this.getDeclaringType() instanceof TypeObject
  }
}

class ConcurrentMethod extends Method {
  ConcurrentMethod() {
    this.getDeclaringType().getQualifiedName().matches("java.util.concurrent%")
  }
}

class CommunicationMethod extends Method {
  CommunicationMethod() {
    this instanceof WaitMethod or
    this instanceof ConcurrentMethod
  }
}

predicate callsCommunicationMethod(Method source) {
  source instanceof CommunicationMethod
  or
  exists(MethodAccess a, Method overridingMethod, Method target |
    callsCommunicationMethod(overridingMethod) and
    overridingMethod.overrides*(target) and
    target = a.getMethod() and
    a.getEnclosingCallable() = source
  )
}

class DangerStmt extends Stmt {
  DangerStmt() {
    exists(SleepMethodAccess sleep | sleep.getEnclosingStmt() = this)
  }
}

from WhileStmt s, DangerStmt d
where 
  d.getParent+() = s and
  not exists(MethodAccess call | callsCommunicationMethod(call.getMethod()) |
    call.getEnclosingStmt().getParent*() = s
  )
select d, "Prefer wait/notify or java.util.concurrent to communicate between threads."
