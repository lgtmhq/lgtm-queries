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
 * @name JSON in JavaScript file
 * @description Storing JSON in files with extension 'js' or 'jsx' is error-prone.
 * @kind problem
 * @problem.severity recommendation
 * @id js/json-in-javascript-file
 * @tags maintainability
 *       language-features
 * @precision very-high
 */

import javascript

from JSONValue v, File f
where f = v.getFile() and
      f.getExtension().regexpMatch("(?i)jsx?") and
      not exists(v.getParent())
select v, "JSON data in file with extension '" + f.getExtension() + "'."