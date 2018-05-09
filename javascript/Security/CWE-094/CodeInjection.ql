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
 * @name Code injection
 * @description Interpreting unsanitized user input as code allows a malicious user arbitrary
 *              code execution.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @id js/code-injection
 * @tags security
 *       external/cwe/cwe-094
 *       external/cwe/cwe-079
 *       external/cwe/cwe-116
 */

import javascript
import semmle.javascript.security.dataflow.CodeInjection::CodeInjection

from Configuration codeInjection, Source source, Sink sink
where codeInjection.hasFlow(source, sink)
select sink, "$@ flows to here and is interpreted as code.", source, "User-provided value"