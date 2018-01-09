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
 * Provides a class for modelling sources of remote user input.
 */

import semmle.javascript.flow.Tracking
import semmle.javascript.frameworks.HTTP
import semmle.javascript.security.dataflow.DOM

/** A data flow source of remote user input. */
abstract class RemoteFlowSource extends DataFlowNode {
  /** Gets a string that describes the type of this remote flow source. */
  abstract string getSourceType();
}


/**
 * An access to `document.cookie`, viewed as a source of remote user input.
 */
private class DocumentCookieSource extends RemoteFlowSource, @propaccess {
  DocumentCookieSource() {
    isDocument(this.(PropAccess).getBase()) and
    this.(PropAccess).getPropertyName() = "cookie"
  }

  override string getSourceType() {
    result = "document.cookie"
  }
}
