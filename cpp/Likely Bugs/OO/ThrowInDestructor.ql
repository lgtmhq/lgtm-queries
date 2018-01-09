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
 * @name Exception thrown in destructor
 * @description Throwing an exception from a destructor may cause immediate
 *              program termination.
 * @kind problem
 * @problem.severity warning
 * @precision very-high
 * @id cpp/throw-in-destructor
 * @tags reliability
 *       readability
 *       language-features
 */
import default

from ThrowExpr t
where t.getEnclosingFunction() instanceof Destructor
  and not t instanceof ReThrowExpr
select t, "Exception thrown in destructor."

