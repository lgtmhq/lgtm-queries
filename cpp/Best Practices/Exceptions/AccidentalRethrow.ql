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
 * @name Accidental rethrow
 * @description When there is nothing to rethrow, attempting to rethrow an exception will terminate the program.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @id cpp/rethrow-no-exception
 * @tags reliability
 *       correctness
 *       exceptions
 */

import default

predicate isInCatch(Expr e) {
  e.getEnclosingStmt().getParent*() instanceof CatchBlock or // Lexically enclosing catch blocks will cause there to be a current exception,
  exists(Function f | f = e.getEnclosingFunction() |
    isInCatch(f.getACallToThisFunction()) or                 // as will dynamically enclosing catch blocks.
    f.getName().toLowerCase().matches("%exception%")         // We assume that rethrows are intended when the function is called *exception*.
  )
}

from ReThrowExpr e
where not isInCatch(e)
select e, "As there is no current exception, this rethrow expression will terminate the program."
