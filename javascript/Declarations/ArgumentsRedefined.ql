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
 * @name Arguments redefined
 * @description The special 'arguments' variable can be redefined, but this should be avoided
 *              since it makes code hard to read and maintain and may prevent compiler
 *              optimizations.
 * @kind problem
 * @problem.severity recommendation
 * @id js/arguments-redefinition
 * @tags efficiency
 *       maintainability
 * @precision very-high
 */

import javascript
import Definitions

from DefiningIdentifier id, string name
where not id.inExternsFile() and
      name = id.getName() and
      (name = "eval" or name = "arguments")
select id, "Redefinition of " + name + "."