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
 * Classes and methods for working with program expressions that denote file system paths.
 */

import Expr

/**
 * An expression that represents a (relative or absolute) file system path.
 */
abstract class PathExpr extends Expr {
  /** Get the path represented by this expression. */
  abstract string getValue();

  /** Get the i-th component of this path. */
  string getComponent(int i) {
    result = getValue().splitAt("/", i)
  }

  /** Get the number of components of this path. */
  int getNumComponent() {
    result = count(getValue().indexOf("/")) + 1
  }

  /** Get the base name of the folder or file this path refers to. */
  string getBaseName() {
    result = getValue().regexpCapture("(.*/|^)([^/]+)", 2)
  }

  /**
   * Resolve the first `n` components of this path.
   */
  Container resolveUpTo(int n) {
    result = resolveUpTo(n, min(int p | exists(resolveUpTo(n, p))))
  }

  /**
   * Resolve the first `n` components of this path relative
   * to the root folder of the given priority.
   *
   * See `Module.searchRoot` for an explanation of roots and priorities.
   */
  Container resolveUpTo(int n, int priority) {
    n = 0 and getTopLevel().(Module).searchRoot(this, (Folder)result, priority) or
    exists (Container base | base = resolveUpTo(n-1, priority) |
      exists (string next | next = getComponent(n-1) |
        // handle empty components and the special "." folder
        (next = "" or next = ".") and result = (Folder)base or
        // handle the special ".." folder
        next = ".." and result = base.getParent() or
        // special handling for Windows drive letters when resolving absolute path:
        // the extractor populates "C:/" as a folder that has path "C:/" but name ""
        (next.regexpMatch("[A-Za-z]:") and base.(Folder).getName() = "" and
         base.getPath() = next.toUpperCase() + "/" and result = base) or
        // default case
        result = base.(Folder).getChild(next)
      )
    )
  }

  /**
   * Resolve this path relative to the root folder of the given priority.
   *
   * See `Module.searchRoot` for an explanation of roots and priorities.
   */
  Container resolve(int priority) {
    result = resolveUpTo(getNumComponent(), priority)
  }

  /** Resolve this path to a file or a folder. */
  Container resolve() {
    result = resolveUpTo(getNumComponent())
  }
}

/**
 * A path expression of the form <code>p + q</code>, where both <code>p</code> and <code>q</code>
 * are path expressions.
 */
library class ConcatPath extends PathExpr, AddExpr {
  ConcatPath() {
    getLeftOperand() instanceof PathExpr and
    getRightOperand() instanceof PathExpr
  }

  string getValue() {
    result = getLeftOperand().(PathExpr).getValue() + getRightOperand().(PathExpr).getValue()
  }

  CFGNode getFirstCFGNode() { result = AddExpr.super.getFirstCFGNode() }
  predicate isImpure() { AddExpr.super.isImpure() }
  string getStringValue() { result = AddExpr.super.getStringValue() }
}
