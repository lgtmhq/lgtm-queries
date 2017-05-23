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
 * @name Use of debugger statement
 * @description The 'debugger' statement should not be used in production code.
 * @kind problem
 * @problem.severity recommendation
 * @tags efficiency
 *       maintainability
 *       language-features
 *       external/cwe/cwe-489
 * @precision very-high
 */

import javascript

from DebuggerStmt ds
select ds, "Do not use 'debugger'."