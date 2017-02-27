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
 * A library for working with the XStream XML serialization framework.
 */

import java

/**
 * The type `com.thoughtworks.xstream.XStream`.
 */
class XStream extends RefType {
  XStream() {
    this.hasQualifiedName("com.thoughtworks.xstream", "XStream")
  }
}

/**
 * An XStream method that deserializes an object.
 */
class XStreamReadObjectMethod extends Method {
  XStreamReadObjectMethod() {
    this.getDeclaringType() instanceof XStream and
    (
      this.hasName("fromXML") or
      this.hasName("unmarshal")
    )
  }
}
