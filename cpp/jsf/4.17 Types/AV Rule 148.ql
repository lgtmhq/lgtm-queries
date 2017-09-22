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
 * @name Use of integer where enum is preferred
 * @description Enumeration types should be used instead of integer types (and constants) to select from a limited series of choices.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @tags maintainability
 *       readability
 *       language-features
 */
import default

// flag switch statements where every non-default case dispatches on an integer constant
from SwitchStmt s
where forex(SwitchCase sc | sc = s.getASwitchCase() and not sc instanceof DefaultCase |
             ((VariableAccess)sc.getExpr()).getTarget().isConst())
      // Allow switch on character types
      and not (s.getExpr().getUnderlyingType().getUnspecifiedType() instanceof CharType)
select s, "Enumeration types should be used instead of integers to select from a limited series of choices."
