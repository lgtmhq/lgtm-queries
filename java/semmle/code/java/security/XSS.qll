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
import semmle.code.java.security.DataFlow

/*
 * Definitions for XSS sinks
 */

class XssSink extends Expr {
  XssSink() {
    exists(HttpServletResponseSendErrorMethod m, MethodAccess ma |
      ma.getMethod() = m and
      this = ma.getArgument(1)
    )
    or exists(ServletWriterSource writer, MethodAccess ma |
      ma.getMethod() instanceof WritingMethod and
      writer.flowsTo(ma.getQualifier()) and
      this = ma.getArgument(_)
    ) or exists(Method m |
      m.getDeclaringType() instanceof TypeWebView and
      (m.getAReference().getArgument(0) = this and m.getName() = "loadData" or
      m.getAReference().getArgument(0) = this and m.getName() = "loadUrl" or
      m.getAReference().getArgument(1) = this and m.getName() = "loadDataWithBaseURL")
    )
  }
}

class WritingMethod extends Method {
  WritingMethod() {
    getDeclaringType().getASupertype*().hasQualifiedName("java.io", _) and
    (
      this.getName().matches("print%") or
      this.getName() = "append" or
      this.getName() = "write"
    )
  }
}


class ServletWriterSource extends FlowSource {
  ServletWriterSource() {
    this.(MethodAccess).getMethod() instanceof ServletResponseGetWriterMethod or
    this.(MethodAccess).getMethod() instanceof ServletResponseGetOutputStreamMethod or
    exists(Method m | m = this.(MethodAccess).getMethod() |
      m.getDeclaringType().getQualifiedName() = "javax.servlet.jsp.JspContext" and
      m.getName() = "getOut"
    )
  }
}
