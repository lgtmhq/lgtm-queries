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

import java
import semmle.code.java.security.DataFlow

/**
 * A call to a `format` or `printf` method.
 */
class StringFormat extends MethodAccess {
  StringFormat() {
    (
      getCallee().hasName("format") or
      getCallee().hasName("printf")
    ) and (
      getCallee().getDeclaringType().hasQualifiedName("java.lang", "String") or
      getCallee().getDeclaringType().hasQualifiedName("java.io", "PrintStream") or
      getCallee().getDeclaringType().hasQualifiedName("java.util", "Formatter")
    )
  }

  Expr getFormatArgument() {
    if getCallee().hasStringSignature("format(Locale, String, Object[])") then
      /*
       * `Formatter` has a special form which takes a `Locale`,
       * which pushes the format argument to the second position.
       */
      result = getArgument(1)
    else
      // In all other cases, we want the first argument.
      result = getArgument(0)
  }
}
