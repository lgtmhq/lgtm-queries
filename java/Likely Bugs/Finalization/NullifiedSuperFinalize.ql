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
 * @name Finalizer inconsistency
 * @description A 'finalize' method that does not call <code>super.finalize</code> may leave
 *              cleanup actions undone.
 * @kind problem
 * @problem.severity error
 * @cwe 568
 */
import default

from FinalizeMethod m, Class c, FinalizeMethod mSuper, Class cSuper
where m.getDeclaringType() = c and
      mSuper.getDeclaringType() = cSuper and
      c.getASupertype+() = cSuper  and
      not cSuper instanceof TypeObject and
      not exists(m.getBody().getAChild())
select m, "Finalize in " + c.getName() + " nullifies finalize in " + cSuper.getName() + "."
