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
 * Provides classes for working with various JavaScript linters.
 */

import javascript

module Linting {
  /**
   * A linter directive that declares one or more global variables.
   */
  abstract class GlobalDeclaration extends Locatable {
    /**
     * Holds if `name` is a global variable declared by this directive, with
     * `writable` indicating whether the variable is declared to be writable or not.
     */
    abstract predicate declaresGlobal(string name, boolean writable);

    /**
     * Holds if this directive applies to statement or expression `s`, meaning that
     * `s` is nested in the directive's scope.
     */
    abstract predicate appliesTo(ExprOrStmt s);

    /**
     * Holds if this directive applies to `gva` and declares the variable it references.
     */
    predicate declaresGlobalForAccess(GlobalVarAccess gva) {
      appliesTo(gva) and declaresGlobal(gva.getName(), _)
    }
  }
}