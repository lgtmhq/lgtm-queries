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
 * @name Thread safety
 * @description Calling Swing methods from a thread other than the event-dispatching thread may
 *              result in multi-threading errors.
 * @kind problem
 * @problem.severity warning
 * @tags reliability
 *       maintainability
 *       frameworks/swing
 */

import java

from MethodAccess ma, Method m, MainMethod main
where ma.getQualifier().getType().getCompilationUnit().getPackage().getName()
        .matches("javax.swing%") and 
      (   m.hasName("show") and m.hasNoParameters()
       or m.hasName("pack") and m.hasNoParameters()
       or m.hasName("setVisible") and m.getNumberOfParameters() = 1) and
      ma.getMethod() = m and
      ma.getEnclosingCallable() = main
select ma, "Call to swing method in " + main.getDeclaringType().getName() 
                                      + " needs to be performed in Swing event thread."
