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
 * @name Clear text storage of sensitive information
 * @description Sensitive information stored without encryption or hashing can expose it to an
 *              attacker.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @id js/clear-text-storage-of-sensitive-data
 * @tags security
 *       external/cwe/cwe-312
 *       external/cwe/cwe-315
 *       external/cwe/cwe-359
 */

import javascript
import semmle.javascript.security.dataflow.CleartextStorage::CleartextStorage

from Configuration cleartextStorage, Source source, Sink sink
where cleartextStorage.hasFlow(source, sink)
select sink, "Sensitive data returned by $@ is stored here.", source, source.describe()
