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
 * @name Use of password hash with insufficient computational effort
 * @description Creating a hash of a password with low computational effort makes the hash vulnerable to password cracking attacks.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @id js/insufficient-password-hash
 * @tags security
 *       external/cwe/cwe-916
 */
import javascript
import semmle.javascript.security.dataflow.RemoteFlowSources
import semmle.javascript.security.dataflow.InsufficientPasswordHash

from InsufficientPasswordHashDataFlowConfiguration insufficientPasswordHash, DataFlowNode source, DataFlowNode sink
where insufficientPasswordHash.flowsFrom(sink, source)
select sink, "Password from $@ is hashed insecurely.", source , source.toString()
