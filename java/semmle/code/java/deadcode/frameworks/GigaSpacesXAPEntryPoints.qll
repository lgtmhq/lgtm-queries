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
 * GigaSpaces XAP (eXtreme Application Platform) is a distributed in-memory "datagrid".
 */

import java
import semmle.code.java.deadcode.DeadCode
import semmle.code.java.frameworks.gigaspaces.GigaSpaces

/**
 * A method that is called during event processing by GigaSpaces, on an event listener class.
 *
 * Note: We do not track registrations of the classes containing these methods. Instead, the method
 * is considered live if the listener is at some point constructed.
 */
class GigaSpacesEventCallableEntryPoint extends CallableEntryPointOnConstructedClass {
  GigaSpacesEventCallableEntryPoint() {
    isGigaSpacesEventMethod(this)
  }
}

/**
 * An event listener class that is reflectively constructed by GigaSpaces to handle event processing.
 */
class GigaSpacesEventDrivenReflectivelyConstructed extends ReflectivelyConstructedClass {
  GigaSpacesEventDrivenReflectivelyConstructed() {
    isGigaSpacesEventDrivenClass(this)
  }
}

/**
 * A method that is called when a GigaSpaces "SpaceClass" is written to, or read from, a space.
 *
 * Note: We do not track whether the space class is written to or read from a space. Instead, the
 * methods are considered live if the space class is at some point constructed.
 */
class GigaSpacesSpaceClassMethodEntryPoint extends CallableEntryPointOnConstructedClass {
  GigaSpacesSpaceClassMethodEntryPoint() {
    this instanceof GigaSpacesSpaceIdGetterMethod or
    this instanceof GigaSpacesSpaceIdSetterMethod or
    this instanceof GigaSpacesSpaceRoutingMethod
  }
}