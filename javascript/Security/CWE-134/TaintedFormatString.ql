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
 * @name Use of externally-controlled format string
 * @description Using external input in format strings can lead to garbled output.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @id js/tainted-format-string
 * @tags security
 *       external/cwe/cwe-134
 */

import javascript
import semmle.javascript.security.dataflow.TaintedFormatString::TaintedFormatString

from Configuration c, DataFlow::Node source, DataFlow::Node sink
where c.hasFlow(source, sink)
select sink, "$@ flows here and is used in a format string.", source, "User-provided value"
