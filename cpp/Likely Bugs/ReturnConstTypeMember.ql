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
 * @name Constant return type on member
 * @description A 'const' modifier on a member function return type is useless. It is usually a typo or misunderstanding, since the syntax for a 'const' function is 'int foo() const', not 'const int foo()'.
 * @kind problem
 * @problem.severity warning
 * @precision very-high
 * @id cpp/member-const-no-effect
 * @tags maintainability
 *       readability
 *       language-features
 */
import ReturnConstTypeCommon

from MemberFunction f, string message
where hasSuperfluousConstReturn(f) and
  if f.hasSpecifier("const") or f.isStatic() then
    message = "The 'const' modifier has no effect on return types. The 'const' modifying the return type can be removed."
  else
    message = "The 'const' modifier has no effect on return types. For a const function, the 'const' should go after the parameter list."
select f, message
