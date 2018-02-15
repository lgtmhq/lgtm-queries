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
 * @name CORS misconfiguration for credentials transfer
 * @description Misconfiguration of CORS HTTP headers allows for leaks of secret credentials.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @id js/cors-misconfiguration-for-credentials
 * @tags security
 *       external/cwe/cwe-346
 *       external/cwe/cwe-639
 */


import javascript
import semmle.javascript.security.dataflow.CorsMisconfigurationForCredentials

from CorsMisconfigurationForCredentialsDataFlowConfiguration cfg, DataFlow::Node source, CorsMisconfigurationForCredentialsSink sink
where cfg.flowsFrom(sink, source)
select sink, "$@ leak vulnerability due to $@.",
       sink.getCredentialsHeader(), "Credential",
       source, "a misconfigured CORS header value"
