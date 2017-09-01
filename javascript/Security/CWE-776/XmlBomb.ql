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
 * @name XML internal entity expansion
 * @description Parsing user input as an XML document with arbitrary internal
 *              entity expansion is vulnerable to denial-of-service attacks.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @id js/xml-bomb
 * @tags security
 *       external/cwe/cwe-776
 *       external/cwe/cwe-400
 */

import javascript
import semmle.javascript.security.dataflow.XmlBomb

from XmlBombTrackingConfig c, DataFlowNode source, DataFlowNode sink
where c.flowsTo(source, sink)
select sink, "A $@ is parsed as XML without guarding against uncontrolled entity expansion.",
       source, "user-provided value"
