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
 * @name Useless return in setter
 * @description Returning a value from a setter function is useless, since it will
 *              always be ignored.
 * @kind problem
 * @problem.severity recommendation
 * @tags maintainability
 *       language-features
 */

import javascript

from FunctionExpr f, ReturnStmt ret
where ret.getContainer() = f and
      f.isSetter() and
      exists (ret.getExpr())
select ret, "Useless return statement in setter function."