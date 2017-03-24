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
 * @name With statement
 * @description The 'with' statement has subtle semantics and should not be used.
 * @kind problem
 * @problem.severity warning
 * @tags maintainability
 *       language-features
 * @precision very-high
 */

import javascript

from WithStmt ws
select ws, "Do not use 'with'."