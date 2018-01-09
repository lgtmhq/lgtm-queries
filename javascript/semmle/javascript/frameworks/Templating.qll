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
 * Provides predicates for working with templating libraries.
 */

import javascript

module Templating {
  /**
   * Gets a string that is a known template delimiter.
   */
  string getADelimiter() {
    result = "<%" or result = "%>" or
    result = "{{" or result = "}}" or
    result = "{%" or result = "%}" or
    result = "<@" or result = "@>" or
    result = "<#" or result = "#>" or
    result = "{#" or result = "#}" or
    result = "{$" or result = "$}" or
    result = "[%" or result = "%]" or
    result = "[[" or result = "]]" or
    result = "<?" or result = "?>"
  }

  /**
   * Gets a regular expression that matches a string containing one
   * of the known template delimiters identified by `getADelimiter()`,
   * storing it in its first (and only) capture group.
   */
  string getDelimiterMatchingRegexp() {
    result = ".*(" + concat("\\Q" + getADelimiter() + "\\E", "|") +  ").*"
  }
}
