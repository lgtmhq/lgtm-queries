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
 * Classes for working with GWT-generated code.
 */

import javascript

/**
 * The `$gwt_version` variable.
 */
class GWTVersionVariable extends GlobalVariable {
  GWTVersionVariable() {
    getName() = "$gwt_version"
  }
}

/**
 * A GWT header script that defines the `$gwt_version` variable.
 */
class GWTHeader extends InlineScript {
  GWTHeader() {
    exists (GWTVersionVariable gwtVersion |
      gwtVersion.getADeclaration().getTopLevel() = this
    )
  }
}

/**
 * A toplevel in a file that appears to be GWT-generated.
 */
class GWTGeneratedTopLevel extends TopLevel {
  GWTGeneratedTopLevel() {
    exists (GWTHeader h | getFile() = h.getFile())
  }
}