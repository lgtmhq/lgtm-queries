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
 * @name CGI script vulnerable to cross-site scripting
 * @description Writing user input directly to a web page
 *              allows for a cross-site scripting vulnerability.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @tags security
 *       external/cwe/cwe-079
 */
import cpp
import semmle.code.cpp.commons.Environment
import semmle.code.cpp.security.TaintTracking

/** A call that prints its arguments to `stdout`. */
class PrintStdoutCall extends FunctionCall {
  PrintStdoutCall() {
    getTarget().hasQualifiedName("puts") or
    getTarget().hasQualifiedName("printf")
  }
}

/** A read of the QUERY_STRING environment variable */
class QueryString extends EnvironmentRead {
  QueryString() {
    getEnvironmentVariable() = "QUERY_STRING"
  }
}

from QueryString query, PrintStdoutCall call, Element printedArg
where call.getAnArgument() = printedArg
  and tainted(query, printedArg)
select printedArg, "Cross-site scripting vulnerability due to $@.",
  query, "this query data"
