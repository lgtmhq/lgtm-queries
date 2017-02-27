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
 * @name Classify files
 * @description This query produces a list of all files in a snapshot
 *              that are classified as generated code, test code or
 *              externs.
 * @kind fileclassifier
 */

import semmle.javascript.GeneratedCode
import semmle.javascript.frameworks.Testing
import semmle.javascript.dependencies.FrameworkLibraries

/**
 * Holds if `f` is classified as belonging to `category`.
 *
 * There are currently four categories:
 *   - `"generated"`: `f` contains generated or minified code;
 *   - `"test"`: `f` contains test code;
 *   - `"externs"`: `f` contains externs declarations;
 *   - `"library"`: `f` contains library code.
 */
predicate classify(File f, string category) {
  isGenerated(f.getATopLevel()) and category = "generated" or
  exists (Test t | t.getFile() = f | category = "test") or
  f.getATopLevel().isExterns() and category = "externs" or
  f.getATopLevel() instanceof FrameworkLibraryInstance and category = "library"
}

from File f, string category
where classify(f, category)
select f, category