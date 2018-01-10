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
 * Provides a helper predicate for encoding external dependency counts.
 */

import semmle.javascript.dependencies.Dependencies

/**
 * Holds if `f` is a file that contains `n` dependencies on `dep` (where `n` is non-zero),
 * and `entity` is the string `p<|>depid<|>depver`, where `p` is the path of `f`
 * relative to the source root, and `depid` and `depver` are the id and version,
 * respectively, of `dep`.
 */
predicate externalDependencies(File f, Dependency dep, string entity, int n) {
  exists (string id, string v | dep.info(id, v) |
    entity = "/" + f.getRelativePath() + "<|>" + id + "<|>" + v
  )
  and
  n = strictcount (Locatable use | use.getFile() = f and use = dep.getAUse(_))
}