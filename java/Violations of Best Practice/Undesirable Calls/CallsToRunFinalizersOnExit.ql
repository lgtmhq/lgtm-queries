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
 * @name Dangerous runFinalizersOnExit
 * @description Calling 'System.runFinalizersOnExit' or 'Runtime.runFinalizersOnExit'
 *              may cause finalizers to be run on live objects, leading to erratic behavior or
 *              deadlock.
 * @kind problem
 * @problem.severity error
 * @tags reliability
 *       maintainability
 */
import java

from MethodAccess ma, Method runfinalizers, Class c
where ma.getMethod() = runfinalizers and
      runfinalizers.hasName("runFinalizersOnExit") and
      runfinalizers.getDeclaringType() = c and
      (   c.hasName("Runtime")
       or c.hasName("System")) and
      c.getPackage().hasName("java.lang") 
select ma, "Call to runFinalizersOnExit."
