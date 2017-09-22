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
 * @name Expression has no effect
 * @description A pure expression whose value is ignored is likely to be the
 *              result of a typo.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @tags maintainability
 *       correctness
 *       external/cwe/cwe-561
 */
import default

class PureExprInVoidContext extends ExprInVoidContext {
  PureExprInVoidContext() { this.isPure() }
}

// loop variable mentioned in the init stmt of a for
predicate accessInInitOfForStmt(Expr e) {
  e instanceof Access and
  exists(ForStmt f, ExprStmt s | f.getInitialization() = s and
                                 s.getExpr() = e)
}

/**
 * Holds if the function `f`, or a function called by it, contains
 * code excluded by the preprocessor.
 */
predicate containsDisabledCode(Function f) {
  // `f` contains a preprocessor branch that was not taken
  exists(PreprocessorBranchDirective pbd |
    f.getBlock().getFile() = pbd.getFile() and
    pbd.getLocation().getStartLine() >= f.getBlock().getLocation().getStartLine() and
    pbd.getLocation().getStartLine() <= f.getBlock().getLocation().getEndLine() and
    (
      pbd.(PreprocessorBranch).wasNotTaken() or

      // an else either was not taken, or it's corresponding branch
      // was not taken.
      pbd instanceof PreprocessorElse
    )
  ) or

  // recurse into function calls
  exists(FunctionCall fc |
    fc.getEnclosingFunction() = f and
    containsDisabledCode(fc.getTarget())
  )
}

from PureExprInVoidContext peivc, Locatable parent,
  Locatable info, string info_text, string tail
where // EQExprs are covered by CompareWhereAssignMeant.ql
      not peivc instanceof EQExpr and
      not accessInInitOfForStmt(peivc) and
      not peivc.isCompilerGenerated() and
      not exists(Macro m | peivc = m.getAnInvocation().getAnExpandedElement()) and
      parent = peivc.getParent() and
      not parent.isInMacroExpansion() and
      not parent instanceof PureExprInVoidContext and
      not peivc.getType() instanceof UnknownType and
      not containsDisabledCode(peivc.(FunctionCall).getTarget()) and
      if peivc instanceof FunctionCall then
        exists(Function target |
          target = peivc.(FunctionCall).getTarget() and
          info = target and
          info_text = target.getName() and
          tail = " (because $@ has no external side effects).")
      else
        (tail = "." and info = peivc and info_text = "")
select peivc, "This expression has no effect" + tail,
       info, info_text
