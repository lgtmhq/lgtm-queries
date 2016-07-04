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
 * @name Random used only once
 * @description Creating an instance of 'Random' for each pseudo-random number required does not 
 *              guarantee an evenly distributed sequence of random numbers.
 * @kind problem
 * @problem.severity warning
 * @cwe 335
 */
import default

from MethodAccess ma, Method random
where random.getDeclaringType().hasQualifiedName("java.util","Random") and
      ma.getMethod() = random and
      ma.getQualifier() instanceof ClassInstanceExpr
select ma, "Random object created and used only once."
