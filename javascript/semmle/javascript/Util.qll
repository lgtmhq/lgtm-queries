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
 * Provides general-purpose utility predicates.
 */

 /**
  * Gets the capitalization of `s`.
  *
  * For example, the capitalization of `"function"` is `"Function"`.
  */
bindingset[s]
string capitalize(string s) {
  result = s.charAt(0).toUpperCase() + s.suffix(1)
}
