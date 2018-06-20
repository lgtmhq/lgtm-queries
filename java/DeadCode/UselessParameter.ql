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
 * @name Useless parameter
 * @description Parameters that are not used add unnecessary complexity to an interface.
 * @kind problem
 * @problem.severity recommendation
 * @precision high
 * @id java/unused-parameter
 * @tags maintainability
 *       useless-code
 *       external/cwe/cwe-561
 */
import semmle.code.java.deadcode.DeadCode

from RootdefCallable c
where not c.whitelisted()
select c.unusedParameter() as p, "The parameter " + p + " is unused."
