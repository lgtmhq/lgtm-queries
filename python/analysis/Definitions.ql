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
 * @name Definitions
 * @description Jump to definition helper query.
 * @kind definitions
 * @id py/jump-to-definition
 */

import python
import DefinitionTracking


from NiceLocationExpr use, Definition defn, string kind, string f, int l
where defn = getUniqueDefinition(use) and kind = "Definition"
and use.hasLocationInfo(f, l, _, _, _) and
// Ignore if the definition is on the same line as the use
not defn.getLocation().hasLocationInfo(f, l, _, _, _)
select use, defn, kind
