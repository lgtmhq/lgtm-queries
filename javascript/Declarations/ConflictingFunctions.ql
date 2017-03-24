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
 * @name Conflicting function declarations
 * @description If two functions with the same name are declared in the same scope, one of the declarations
 *              overrides the other without warning. This makes the code hard to read and maintain, and
 *              may even lead to platform-dependent behavior.
 * @kind problem
 * @problem.severity error
 * @tags reliability
 *       correctness
 * @precision high
 */

import javascript

from FunctionDeclStmt f, FunctionDeclStmt g
where f.getVariable() = g.getVariable() and
      // ignore global functions; conflicts across scripts are usually false positives
      not f.getVariable().isGlobal() and
      // only report each pair once
      f.getLocation().startsBefore(g.getLocation())
select f.getId(), "Declaration of " + f.describe() + " conflicts with $@ in the same scope.", g.getId(), "another declaration"