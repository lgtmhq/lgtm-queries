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
 * @name Short global name
 * @description Global variables should have descriptive names, to help document their use, avoid namespace pollution and reduce the risk of shadowing with local variables.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @id cpp/short-global-name
 * @tags maintainability
 */
import default

from GlobalVariable gv
where gv.getName().length() <= 3
  and not gv.isStatic()
select gv, "Poor global variable name '" + gv.getName() + "'. Prefer longer, descriptive names for globals (eg. kMyGlobalConstant, not foo)."
