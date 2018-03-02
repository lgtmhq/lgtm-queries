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
 * @name Insecure randomness
 * @description Using a cryptographically weak pseudo-random number generator to generate a
 *              security-sensitive value may allow an attacker to predict what value will
 *              be generated.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @id js/insecure-randomness
 * @tags security
 *       external/cwe/cwe-338
 */
import javascript
import semmle.javascript.security.dataflow.InsecureRandomness

from InsecureRandomnessDataFlowConfiguration cfg, DataFlow::Node source, DataFlow::Node sink
where cfg.flowsFrom(sink, source)
select sink, "Cryptographically insecure $@ in a security context.", source, "random value"