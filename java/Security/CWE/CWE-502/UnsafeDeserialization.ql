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
 * @name Deserialization of user-controlled data
 * @description Deserializing user-controlled data may allow attackers to
 *              execute arbitrary code.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @id java/unsafe-deserialization
 * @tags security
 *       external/cwe/cwe-502
 */
import java
import semmle.code.java.dataflow.FlowSources
import UnsafeDeserialization

class UnsafeDeserializationConfig extends TaintTracking::Configuration {
  UnsafeDeserializationConfig() { this = "UnsafeDeserializationConfig" }
  override predicate isSource(DataFlow::Node source) { source instanceof RemoteUserInput }
  override predicate isSink(DataFlow::Node sink) { sink instanceof UnsafeDeserializationSink }
}

from UnsafeDeserializationSink sink, RemoteUserInput source, UnsafeDeserializationConfig conf
where conf.hasFlow(source, sink)
select sink.getMethodAccess(), "Unsafe deserialization of $@.", source, "user input"
