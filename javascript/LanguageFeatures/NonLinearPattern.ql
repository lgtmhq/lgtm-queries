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
 * @name Non-linear pattern
 * @description If the same pattern variable appears twice in an array or object pattern,
 *              the second binding will silently overwrite the first binding, which is probably
 *              unintentional.
 * @kind problem
 * @problem.severity error
 * @id js/non-linear-pattern
 * @tags reliability
 *       correctness
 *       language-features
 * @precision very-high
 */

import javascript

from BindingPattern p, string n, VarDecl v, VarDecl w
where v = p.getABindingVarRef() and w = p.getABindingVarRef() and
      v.getName() = n and w.getName() = n and
      v != w and
      v.getLocation().startsBefore(w.getLocation())
select w, "Repeated binding of pattern variable '" + n + "' previously bound $@.", v, "here"
