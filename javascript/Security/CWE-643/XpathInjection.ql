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
 * @name XPath injection
 * @description Building an XPath expression from user-controlled sources is vulnerable to insertion of
 *              malicious code by the user.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @id js/xpath-injection
 * @tags security
 *       external/cwe/cwe-643
 */

import javascript
import semmle.javascript.security.dataflow.XpathInjection::XpathInjection

from Configuration c, DataFlow::Node source, DataFlow::Node sink
where c.hasFlow(source, sink)
select sink, "$@ flows here and is used in an XPath expression.", source, "User-provided value"
