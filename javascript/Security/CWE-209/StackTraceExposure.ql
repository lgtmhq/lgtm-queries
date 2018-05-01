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
 * @name Information exposure through a stack trace
 * @description Propagating stack trace information to an external user can
 *              unintentionally reveal implementation details that are useful
 *              to an attacker for developing a subsequent exploit.
 * @kind problem
 * @problem.severity warning
 * @precision very-high
 * @id js/stack-trace-exposure
 * @tags security
 *       external/cwe/cwe-209
 */

import javascript
import semmle.javascript.security.dataflow.StackTraceExposure::StackTraceExposure

from Configuration cfg, Source source, Sink sink
where cfg.flowsFrom(sink, source)
select sink, "Stack trace information from $@ may be exposed to an external user here.",
       source, "here"