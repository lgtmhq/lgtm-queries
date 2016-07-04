// Copyright 2016 Semmle Ltd.
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
 * @name Duplicate parameter names
 * @description If a function has two parameters with the same name, the second parameter shadows the first one,
 *              which makes the code hard to understand and error-prone.
 * @kind problem
 * @problem.severity error
 */

import javascript

/** The <code>i</code>-th parameter of <code>f</code>, viz. <code>p</code>, binds a variable <code>name</code>. */
predicate parmBinds(Function f, int i, Parameter p, string name) {
  p = f.getParameter(i) and
  p.getAVariable().getName() = name
}

from Function f, Parameter p, Parameter q, int i, int j, string name
where parmBinds(f, i, p, name) and
      parmBinds(f, j, q, name) and
      i < j and
      j = max(int k | parmBinds(f, k, _, name) | k)
select p, "This parameter has the same name as $@ of the same function.", q, "another parameter"
