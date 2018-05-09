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
 * @name Client-side URL redirect
 * @description Client-side URL redirection based on unvalidated user input
 *              may cause redirection to malicious web sites.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @id js/client-side-unvalidated-url-redirection
 * @tags security
 *       external/cwe/cwe-079
 *       external/cwe/cwe-116
 *       external/cwe/cwe-601
 */

import javascript
import semmle.javascript.security.dataflow.ClientSideUrlRedirect::ClientSideUrlRedirect

from Configuration urlRedirect, Source source, Sink sink
where urlRedirect.hasFlow(source, sink)
select sink, "Untrusted URL redirection due to $@.", source, "user-provided value"