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
 * @name Uncontrolled data used in path expression
 * @description Accessing paths influenced by users can allow an attacker to access unexpected resources.
 * @kind problem
 * @problem.severity error
 * @sub-severity high
 * @precision medium
 * @id py/path-injection
 * @tags correctness
 *       security
 *       external/owasp/owasp-a1
 *       external/cwe/cwe-022
 *       external/cwe/cwe-023
 *       external/cwe/cwe-036
 *       external/cwe/cwe-073
 *       external/cwe/cwe-099
 */

import python

/* Sources */
import semmle.python.web.HttpRequest

/* Sinks */
import semmle.python.security.injection.Path


from TaintSource src, TaintSink sink
where src.flowsToSink(sink)

select sink, "This path depends on $@.", src, "a user-provided value"
