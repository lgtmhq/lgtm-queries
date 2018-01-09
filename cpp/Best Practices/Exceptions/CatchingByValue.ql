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
 * @name Catching by value
 * @description Catching an exception by value will create a copy of the thrown exception, thereby potentially slicing the original exception object.
 * @kind problem
 * @problem.severity warning
 * @precision very-high
 * @id cpp/catch-by-value
 * @tags efficiency
 *       correctness
 *       exceptions
 */

import default

from CatchBlock cb, Class caughtType
where caughtType = cb.getParameter().getType().getUnderlyingType().getUnspecifiedType()
select cb, "This should catch a " + caughtType.getName() + " by (const) reference rather than by value."
