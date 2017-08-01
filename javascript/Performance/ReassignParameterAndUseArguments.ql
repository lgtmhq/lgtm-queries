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
 * @name Parameter reassigned in function that uses arguments
 * @description A function that reassigns one of its parameters and also uses the arguments object
 *              may not be optimized properly.
 * @kind problem
 * @problem.severity recommendation
 * @id js/parameter-reassignment-with-arguments
 * @tags efficiency
 *       maintainability
 * @precision very-high
 */

import javascript

from Function f, SimpleParameter p, VarAccess assgn
where p = f.getAParameter() and
      f.usesArgumentsObject() and
      assgn = p.getVariable().getAnAccess() and
      assgn.isLValue()
select p, "This parameter is reassigned $@, " +
          "which may prevent optimization because the surrounding function " +
          "uses the arguments object.", assgn, "here"