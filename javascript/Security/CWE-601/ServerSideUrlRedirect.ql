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
 * @name Server-side URL redirect
 * @description Server-side URL redirection based on unvalidated user input
 *              may cause redirection to malicious web sites.
 * @kind problem
 * @problem.severity warning
 * @tags security
 *       external/cwe/cwe-601
 * @precision medium
 */

import javascript
import semmle.javascript.security.dataflow.ServerSideUrlRedirect

from ServerSideUrlRedirectDataFlowConfiguration urlRedirect, DataFlowNode source, DataFlowNode sink
where urlRedirect.flowsTo(source, sink)
select sink, "Untrusted URL redirection due to $@.", source, "user-provided value"
