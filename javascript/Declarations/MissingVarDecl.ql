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
 * @name Missing variable declaration
 * @description If a variable is not declared as a local variable, it becomes a global variable by default, which
 *              may be unintentional and could lead to unexpected behavior.
 * @kind problem
 * @problem.severity error
 */

import javascript

/**
 * Find undeclared globals in `f`, that is, global variables that are accessed in `f`,
 * but not declared in the same toplevel as `f`.
 */
GlobalVariable undeclaredGlobalIn(Function f) {
  result.getAnAccess().getEnclosingFunction() = f and
  not result.declaredIn(f.getTopLevel())
}

/**
 * Find accidental globals in `f`, that is, undeclared globals in `f` that are not
 * live at the entry of `f` (meaning the first access to them is always a write).
 */
GlobalVariable accidentalGlobalIn(Function f) {
  result = undeclaredGlobalIn(f) and
  not f.getEntryBB().isLiveAtEntry(result)
}

/**
 * Find accidental globals in `f` that are accessed at least once in reachable
 * code.
 *
 * This prevents duplication of results between this query and the (simpler)
 * 'Unused variable' query.
 */
GlobalVariable candidateVariable(Function f) {
  result = accidentalGlobalIn(f) and
  f.getEntryBB().getASuccessor*().getANode() = result.getAnAccess()
}

/**
 * Get an access to `v` in function `f` at line `line` and column `column`.
 */
GlobalVarAccess getAccessAt(GlobalVariable v, Function f, int line, int column) {
  result.getEnclosingFunction() = f and
  result = v.getAnAccess() and
  exists (Location loc | loc = result.getLocation() |
    line = loc.getStartLine() and
    column = loc.getStartColumn()
  )
}
 
/**
 * Get the (lexically) first access to variable `v` in function `f`.
 */
GlobalVarAccess getFirstAccessIn(GlobalVariable v, Function f) {
  exists (int l, int c |
    result = getAccessAt(v, f, l, c) and
    l = min (int ll | exists (getAccessAt(v, f, ll, _))) and
    c = min (int cc | exists (getAccessAt(v, f, l, cc)))
  )
}

from Function f, GlobalVariable gv
where gv = candidateVariable(f)
select getFirstAccessIn(gv, f), "Variable " + gv.getName() + " is used like a local variable, but is missing a declaration."
