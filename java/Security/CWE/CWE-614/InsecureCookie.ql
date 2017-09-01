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
 * @name Failure to use secure cookies
 * @description Insecured cookies may be sent in cleartext, which makes them vulnerable to
 *              interception.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @id java/insecure-cookie
 * @tags security
 *       external/cwe/cwe-614
 */
import java
import semmle.code.java.frameworks.Servlets

from MethodAccess add
where
  add.getMethod() instanceof ResponseAddCookieMethod and
  not exists(Variable cookie, MethodAccess m | 
    add.getArgument(0) = cookie.getAnAccess() and
    m.getMethod().getName() = "setSecure" and 
    m.getArgument(0).(BooleanLiteral).getBooleanValue() = true and
    m.getQualifier() = cookie.getAnAccess()
  )
select add, "Cookie is added to response without the 'secure' flag being set."
