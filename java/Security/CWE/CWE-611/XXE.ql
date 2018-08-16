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
 * @name Resolving XML external entity in user-controlled data
 * @description Parsing user-controlled XML documents and allowing expansion of external entity
 * references may lead to disclosure of confidential data or denial of service.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @id java/xxe
 * @tags security
 *       external/cwe/cwe-611
 */

import java
import XmlParsers
import semmle.code.java.dataflow.FlowSources

class SafeSAXSourceFlowConfig extends TaintTracking::Configuration2 {
  SafeSAXSourceFlowConfig() { this = "XmlParsers::SafeSAXSourceFlowConfig" }
  override predicate isSource(DataFlow::Node src) { src.asExpr() instanceof SafeSAXSource }
  override predicate isSink(DataFlow::Node sink) { sink.asExpr() = any(XmlParserCall parse).getSink() }
  override int fieldFlowBranchLimit() { result = 0 }
}

class UnsafeXxeSink extends DataFlow::ExprNode {
  UnsafeXxeSink() {
    not exists(SafeSAXSourceFlowConfig safeSource | safeSource.hasFlowTo(this)) and
    exists(XmlParserCall parse |
      parse.getSink() = this.getExpr() and
      not parse.isSafe()
    )
  }
}

class XxeConfig extends TaintTracking::Configuration {
  XxeConfig() { this = "XXE.ql::XxeConfig" }
  override predicate isSource(DataFlow::Node src) { src instanceof RemoteUserInput }
  override predicate isSink(DataFlow::Node sink) { sink instanceof UnsafeXxeSink }
}

from UnsafeXxeSink sink, RemoteUserInput source, XxeConfig conf
where conf.hasFlow(source, sink)
select sink, "Unsafe parsing of XML file from $@.", source, "user input"
