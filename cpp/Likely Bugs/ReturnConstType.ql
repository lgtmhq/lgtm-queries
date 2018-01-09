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
 * @name Constant return type
 * @description A 'const' modifier on a function return type is useless and should be removed for clarity.
 * @kind problem
 * @problem.severity warning
 * @precision very-high
 * @id cpp/non-member-const-no-effect
 * @tags maintainability
 *       readability
 *       language-features
 */
import ReturnConstTypeCommon

from Function f
where hasSuperfluousConstReturn(f)
  and not f instanceof MemberFunction
select f, "The 'const' modifier has no effect on a return type and can be removed."
