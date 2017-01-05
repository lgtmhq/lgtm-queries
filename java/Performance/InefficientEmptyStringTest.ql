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
 * @name Inefficient empty string test
 * @description Checking a string for equality with an empty string is inefficient.
 * @kind problem
 * @problem.severity recommendation
 * @tags efficiency
 *       maintainability
 */
import java

from MethodAccess mc
where mc.getQualifier().getType() instanceof TypeString and
      mc.getMethod().hasName("equals") and
      (mc.getArgument(0).(StringLiteral).getLiteral() = "\"\"" or
       mc.getQualifier().(StringLiteral).getLiteral() = "\"\"")
select mc, "Inefficient comparison to empty string, "
           + "check for zero length instead."
