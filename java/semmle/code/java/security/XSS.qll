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

import java
import semmle.code.java.frameworks.Servlets
import semmle.code.java.frameworks.android.WebView
import semmle.code.java.dataflow.TaintTracking

/*
 * Definitions for XSS sinks
 */

class XssSink extends DataFlow::ExprNode {
  XssSink() {
    exists(HttpServletResponseSendErrorMethod m, MethodAccess ma |
      ma.getMethod() = m and
      this.getExpr() = ma.getArgument(1)
    )
    or exists(ServletWriterSourceToWritingMethodFlowConfig writer, MethodAccess ma |
      ma.getMethod() instanceof WritingMethod and
      writer.hasFlowToExpr(ma.getQualifier()) and
      this.getExpr() = ma.getArgument(_)
    ) or exists(Method m |
      m.getDeclaringType() instanceof TypeWebView and
      (m.getAReference().getArgument(0) = this.getExpr() and m.getName() = "loadData" or
      m.getAReference().getArgument(0) = this.getExpr() and m.getName() = "loadUrl" or
      m.getAReference().getArgument(1) = this.getExpr() and m.getName() = "loadDataWithBaseURL")
    )
  }
}

class ServletWriterSourceToWritingMethodFlowConfig extends TaintTracking::Configuration {
  ServletWriterSourceToWritingMethodFlowConfig() { this = "XSS::ServletWriterSourceToWritingMethodFlowConfig" }
  override predicate isSource(DataFlow::Node src) { src.asExpr() instanceof ServletWriterSource }
  override predicate isSink(DataFlow::Node sink) { exists(MethodAccess ma | sink.asExpr() = ma.getQualifier() and ma.getMethod() instanceof WritingMethod) }
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

class ServletWriterSource extends MethodAccess {
  ServletWriterSource() {
    this.getMethod() instanceof ServletResponseGetWriterMethod or
    this.getMethod() instanceof ServletResponseGetOutputStreamMethod or
    exists(Method m | m = this.getMethod() |
      m.getDeclaringType().getQualifiedName() = "javax.servlet.jsp.JspContext" and
      m.getName() = "getOut"
    )
  }
}
