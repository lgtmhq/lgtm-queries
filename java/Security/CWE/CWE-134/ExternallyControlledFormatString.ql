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
 * @description Using external input in format strings can lead to exceptions or information leaks.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @id java/tainted-format-string
 * @tags security
 *       external/cwe/cwe-134
 */

import java
import semmle.code.java.dataflow.FlowSources
import semmle.code.java.StringFormat

from RemoteUserInput source, StringFormat formatCall
where source.flowsTo(DataFlow::exprNode(formatCall.getFormatArgument()))
select formatCall.getFormatArgument(),
  "$@ flows to here and is used in a format string.",
  source, "User-provided value"
