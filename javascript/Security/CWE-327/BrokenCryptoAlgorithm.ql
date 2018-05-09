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
 * @name Use of a broken or weak cryptographic algorithm
 * @description Using broken or weak cryptographic algorithms can compromise security.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @id js/weak-cryptographic-algorithm
 * @tags security
 *       external/cwe/cwe-327
 */
import javascript
import semmle.javascript.security.dataflow.RemoteFlowSources
import semmle.javascript.security.dataflow.BrokenCryptoAlgorithm::BrokenCryptoAlgorithm
import semmle.javascript.security.SensitiveActions

from Configuration brokenCrypto, Source source, Sink sink
where brokenCrypto.hasFlow(source, sink) and
      not source.asExpr() instanceof CleartextPasswordExpr // flagged by js/insufficient-password-hash
select sink, "Sensitive data from $@ is used in a broken or weak cryptographic algorithm.", source , source.describe()
