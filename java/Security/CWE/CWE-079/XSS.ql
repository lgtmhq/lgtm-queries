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
 * @name Cross-site scripting
 * @description Writing user input directly to a web page
 *              allows for a cross-site scripting vulnerability.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @id java/xss
 * @tags security
 *       external/cwe/cwe-079
 */
import java
import semmle.code.java.dataflow.FlowSources
import semmle.code.java.security.XSS

class XSSConfig extends TaintTracking::Configuration2 {
  XSSConfig() { this = "XSSConfig" }
  override predicate isSource(DataFlow::Node source) { source instanceof RemoteUserInput }
  override predicate isSink(DataFlow::Node sink) { sink instanceof XssSink }
  override predicate isSanitizer(DataFlow::Node node) { node.getType() instanceof NumericType or node.getType() instanceof BooleanType }
}

from XssSink sink, RemoteUserInput source, XSSConfig conf
where conf.hasFlow(source, sink)
select sink, "Cross-site scripting vulnerability due to $@.",
  source, "user-provided value"
