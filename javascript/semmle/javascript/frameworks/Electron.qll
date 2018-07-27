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

import javascript

module Electron {
  /**
   * A data flow node that is an Electron `webPreferences` property.
   */
  class WebPreferences extends DataFlow::ObjectLiteralNode {
    WebPreferences() {
      exists(BrowserObject bo | this = bo.getOptionArgument(0, "webPreferences").getALocalSource())
    }
  }
  
  /**
   * A data flow node that creates a new `BrowserWindow` or `BrowserView`.
   */
  private abstract class BrowserObject extends DataFlow::NewNode {
  }
  
  /**
   * A data flow node that creates a new `BrowserWindow`.
   */
  class BrowserWindow extends BrowserObject {
    BrowserWindow() {
      this = DataFlow::moduleMember("electron", "BrowserWindow").getAnInstantiation()
    }
  }
  
  /**
   * A data flow node that creates a new `BrowserView`.
   */
  class BrowserView extends BrowserObject {
    BrowserView() {
      this = DataFlow::moduleMember("electron", "BrowserView").getAnInstantiation()
    }
  }
}