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
 * @name Bad implementation of an event Adapter
 * @description In a class that extends a Swing or Abstract Window Toolkit event adapter, an
 *              event handler that does not have exactly the same name as the event handler that it
 *              overrides means that the overridden event handler is not called.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @tags reliability
 *       maintainability
 *       frameworks/swing
 */
import java

class Adapter extends Class {
  Adapter() {
    this.getName().matches("%Adapter") and
    (   this.getPackage().hasName("java.awt.event")
     or this.getPackage().hasName("javax.swing.event"))
  }
}

from Class c, Adapter adapter, Method m
where adapter = c.getASupertype() and 
      c = m.getDeclaringType() and
      exists (Method original | adapter = original.getDeclaringType() |
        m.getName() = original.getName()
      ) and
      not exists(Method overridden | adapter = overridden.getDeclaringType() |
        m.overrides(overridden)
      ) and
      // The method is not used for any other purpose.
      not exists(MethodAccess ma | ma.getMethod() = m)
select m, "Method " + m.getName() + " attempts to override a method in " + adapter.getName() + 
          ", but does not have the same argument types. " + m.getName() + " will not be called when an event occurs."
