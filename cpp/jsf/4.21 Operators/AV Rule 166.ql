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
 * @name Sizeof with side effects
 * @description The sizeof operator should not be used on expressions that contain side effects. It is subtle whether the side effects will occur or not.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @id cpp/sizeof-side-effect
 * @tags reliability
 *       correctness
 */
import default
import jsf.lib.section_4_21_Operators.AV_Rule_166

from SizeofImpureExprOperator sz
select sz, "A sizeof operator should not be used on expressions that contain side effects as the effect is confusing."
