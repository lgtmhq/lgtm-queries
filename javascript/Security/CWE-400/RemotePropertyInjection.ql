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
 * @name Remote property injection
 * @description Allowing writes to arbitrary properties or calls to arbitrary 
 *       methods of an object may lead to denial-of-service attacks. 
 *   
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @id js/remote-property-injection
 * @tags security
 *       external/cwe/cwe-250
 *       external/cwe/cwe-400
  */

import javascript
import semmle.javascript.security.dataflow.RemotePropertyInjection::RemotePropertyInjection

from Configuration c, DataFlow::Node source, Sink sink
where c.hasFlow(source, sink)  
select sink, "A $@ is used as" + sink.getMessage(),
       source, "user-provided value"
       
