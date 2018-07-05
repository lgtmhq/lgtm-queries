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
 * @name Hard-coded credentials
 * @description Hard-coding credentials in source code may enable an attacker
 *              to gain unauthorized access.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @id js/hardcoded-credentials
 * @tags security
 *       external/cwe/cwe-259
 *       external/cwe/cwe-321
 *       external/cwe/cwe-798
 */

import javascript
private import semmle.javascript.security.dataflow.HardcodedCredentials::HardcodedCredentials

from Configuration cfg, DataFlow::Node source, Sink sink, string value
where cfg.hasFlow(source, sink) and
      // use source value in message if it's available
      if source.asExpr() instanceof ConstantString then
        value = "The hard-coded value \"" + source.asExpr().(ConstantString).getStringValue() + "\""
      else
        value = "This hard-coded value"
select source, value + " is used as $@.", sink, sink.getKind()
