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
 * A library for computing metrics on Java statements.
 */

import semmle.code.java.Statement

/** This class provides access to metrics information for statements. */
class MetricStmt extends Stmt {

  /** A nesting depth of this statement. */
  int getANestingDepth() {
    not exists(Stmt s | s.getParent() = this) and result = 0
    or result = ((MetricStmt)this.getAChild()).getANestingDepth() + 1
  }

  /** The maximum nesting depth of this statement. */
  int getNestingDepth() {
    result = max(this.getANestingDepth())
  }

  /** The nested depth of this statement. */
  int getNestedDepth() {
    not exists(Stmt s | s = this.getParent()) and result = 0
    or exists(MetricStmt s | s = this.getParent() and result = s.getNestedDepth() + 1)
  }
}
