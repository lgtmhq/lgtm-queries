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

import default
import semmle.code.java.frameworks.Servlets
import semmle.code.java.security.DataFlow

/**
 * Header-splitting sinks. Expressions that end up in an HTTP header.
 */
class HeaderSplittingSink extends Expr {
  HeaderSplittingSink() {
    exists(ResponseAddCookieMethod m, MethodAccess ma |
      ma.getMethod() = m and
      this = ma.getArgument(0)
    )
    or exists(ResponseAddHeaderMethod m, MethodAccess ma |
      ma.getMethod() = m and
      this = ma.getAnArgument()
    )
    or exists(ResponseSetHeaderMethod m, MethodAccess ma |
      ma.getMethod() = m and
      this = ma.getAnArgument()
    )
    or exists(JaxRsResponseBuilder builder, Method m |
      m = builder.getAMethod() and m.getName() = "header" |
      this = m.getAReference().getArgument(1)
    )
  }
}

class WhitelistedSource extends RemoteUserInput {
  WhitelistedSource() {
    this.(MethodAccess).getMethod() instanceof HttpServletRequestGetHeaderMethod
  }
}
