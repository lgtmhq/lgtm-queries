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

/* Remote Method Invocation. */

import java

/** The interface `java.rmi.Remote`. */
class TypeRemote extends RefType {
  TypeRemote() {
    hasQualifiedName("java.rmi", "Remote")
  }
}

/** A method that is intended to be called via RMI. */
class RemoteCallableMethod extends Method {
  RemoteCallableMethod() {
    remoteCallableMethod(this)
  }
}

private predicate remoteCallableMethod(Method method) {
  method.getDeclaringType().getASupertype() instanceof TypeRemote
  or exists (Method meth | remoteCallableMethod(meth) and method.getAnOverride() = meth)
}
