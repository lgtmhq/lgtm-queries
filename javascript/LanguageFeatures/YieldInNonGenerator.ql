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
 * @name Yield in non-generator function
 * @description 'yield' should only be used in generator functions.
 * @kind problem
 * @problem.severity error
 * @tags maintainability
 *       language-features
 */

import javascript

from YieldExpr yield, Function f
where f = yield.getEnclosingFunction() and
      not f.isGenerator()
select yield, "This yield expression is contained in $@ which is not marked as a generator.",
       f.getFirstToken(), "a function"