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
 * @name Unused variable
 * @description Unused variables may be a symptom of a bug and should be examined carefully.
 * @kind problem
 * @problem.severity recommendation
 * @tags maintainability
 */

import javascript

from VarDecl vd, Variable v
where v = vd.getVariable() and
      not v.isGlobal() and
      not exists(v.getAnAccess()) and
      not exists (Parameter p | v = p.getAVariable()) and
      not vd.getParent() instanceof FunctionExpr and
      not exists (ExportNamedDeclaration end | vd = end.getADecl()) and
      // exclude variables mentioned in JSDoc comments in externs
      not exists (Externs ext, JSDoc jsdoc |
        ext = vd.getTopLevel() and jsdoc.getComment().getTopLevel() = ext |
        jsdoc.getComment().getText().regexpMatch("(?s).*\\b" + v.getName() + "\\b.*")
      ) and
      // `v` isn't used in combination with a rest property pattern to filter out unwanted properties
      not exists (ObjectPattern op | exists(op.getRest()) |
        op.getAPropertyPattern().getValuePattern() = vd
      )
select vd, "Unused variable."