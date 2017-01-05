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
 * @name Information exposure through a stack trace
 * @description Information from a stack trace propagates to an external user.
 *              Stack traces can unintentionally reveal implementation details
 *              that are useful to an attacker for developing a subsequent exploit.
 * @kind problem
 * @problem.severity error
 * @tags security
 *       external/cwe/cwe-209
 *       external/cwe/cwe-497
 */

import java
import semmle.code.java.security.DataFlow
import semmle.code.java.security.XSS

/**
 * One of the `printStackTrace()` overloads on `Throwable`.
 */
class PrintStackTraceMethod extends Method {
  PrintStackTraceMethod() {
    getDeclaringType().hasQualifiedName("java.lang", "Throwable") and
    getName() = "printStackTrace"
  }
}

/**
 * A call that uses `Throwable.printStackTrace()` on a stream that is connected
 * to external output.
 */
predicate printsStackToWriter(MethodAccess call) {
  exists (ServletWriterSource writerSource, PrintStackTraceMethod printStackTrace |
    call.getMethod() = printStackTrace and
    writerSource.flowsTo(call.getAnArgument())
  )
}

/**
 * A `PrintWriter` that wraps a given string writer. This pattern is used
 * in the most common idiom for converting a `Throwable` to a string.
 */
predicate printWriterOnStringWriter(Expr printWriter, Variable stringWriterVar) {
  printWriter.getType().(Class).hasQualifiedName("java.io", "PrintWriter") and
  stringWriterVar.getType().(Class).hasQualifiedName("java.io", "StringWriter") and (
    printWriter.(ClassInstanceExpr).getAnArgument() = stringWriterVar.getAnAccess() or
    printWriterOnStringWriter(printWriter.(VarAccess).getVariable().getInitializer(), stringWriterVar)
  )
}

predicate stackTraceExpr(Expr exception, MethodAccess stackTraceString) {
  exists (Expr printWriter, Variable stringWriterVar, MethodAccess printStackCall |
    printWriterOnStringWriter(printWriter, stringWriterVar) and
    printStackCall.getMethod() instanceof PrintStackTraceMethod and
    printStackCall.getAnArgument() = printWriter and
    printStackCall.getQualifier() = exception and
    stackTraceString.getQualifier() = stringWriterVar.getAnAccess() and
    stackTraceString.getMethod().getName() = "toString" and
    stackTraceString.getMethod().getNumberOfParameters() = 0
  )
}

class StackTraceStringFlowSource extends FlowSource {
  StackTraceStringFlowSource() {
    stackTraceExpr(_, this)
  }
}

/**
 * A write of stack trace data to an external stream.
 */
predicate printsStackExternally(MethodAccess call, Expr stackTrace) {
  printsStackToWriter(call) and
  call.getQualifier() = stackTrace
}

/**
 * A stringified stack trace flows to an external sink.
 */
predicate stringifiedStackFlowsExternally(XssSink externalExpr, Expr stackTrace) {
  exists (StackTraceStringFlowSource stackTraceString |
    stackTraceExpr(stackTrace, stackTraceString) and
    stackTraceString.flowsTo(externalExpr)
  )
}

class GetMessageFlowSource extends FlowSource {
  GetMessageFlowSource() {
    exists (Method method |
      method = this.(MethodAccess).getMethod() and
      method.hasName("getMessage") and
      method.hasNoParameters() and
      method.getDeclaringType().hasQualifiedName("java.lang", "Throwable")
    )
  }
}

/**
 * A call to `getMessage()` that then flows to a servlet response.
 */
predicate getMessageFlowsExternally(XssSink externalExpr, GetMessageFlowSource getMessage) {
  getMessage.flowsTo(externalExpr)
}

from Expr externalExpr, Expr errorInformation
where
  printsStackExternally(externalExpr, errorInformation) or
  stringifiedStackFlowsExternally(externalExpr, errorInformation) or
  getMessageFlowsExternally(externalExpr, errorInformation)
select
  externalExpr, "$@ can be exposed to an external user.",
  errorInformation, "Error information"
