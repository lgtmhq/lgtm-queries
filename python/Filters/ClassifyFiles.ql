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
 *              that are classified as generated code or test code.
 * @kind fileclassifier
 */

import python
import semmle.python.filters.GeneratedCode
import semmle.python.filters.Tests

predicate classify(File f, string tag) {
  f instanceof GeneratedFile and tag = "generated" or
  exists (TestScope t | t.getLocation().getFile() = f) and tag = "test"
}

from File f, string tag
where classify(f, tag)
select f, tag