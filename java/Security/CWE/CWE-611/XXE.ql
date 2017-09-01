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
 * @name Resolving XML external entity in user-controlled data
 * @description Parsing user-controlled XML documents and allowing expansion of external entity
 * references may lead to disclosure of confidential data or denial of service.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @id java/xxe
 * @tags security
 *       external/cwe/cwe-611
 */

import java
import XmlParsers
import semmle.code.java.security.DataFlow

class UnsafeXxeSink extends Expr {
  UnsafeXxeSink() {
    not exists(SafeSAXSource safeSource | safeSource.flowsTo(this)) and
    exists(XmlParserCall parse |
      parse.getSink() = this and
      not parse.isSafe()
    )
  }
}

from UnsafeXxeSink sink, RemoteUserInput source
where source.flowsTo(sink)
select sink, "Unsafe parsing of XML file from $@.", source, "user input"
