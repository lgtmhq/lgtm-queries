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

import javascript

/** An error encountered during extraction. */
abstract class Error extends Locatable {
  /** Get the message associated with this error. */
  abstract string getMessage();
  
  string toString() {
    result = getMessage()
  }
}

/** A JavaScript parse error encountered during extraction. */
class JSParseError extends @js_parse_error, Error {
  /** Get the toplevel element this error occurs in. */
  TopLevel getTopLevel() {
    jsParseErrors(this, result, _)
  }

  string getMessage() {
    jsParseErrors(this, _, result)
  }
}