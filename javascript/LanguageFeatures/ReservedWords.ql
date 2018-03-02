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
 * @name Reserved word used as variable name
 * @description Future reserved words should not be used as variable names.
 * @kind problem
 * @problem.severity recommendation
 * @id js/use-of-reserved-word
 * @tags maintainability
 *       language-features
 * @precision very-high
 */

import javascript

from Identifier id
where id.getName().regexpMatch("class|const|enum|export|extends|import|super|implements|interface|let|package|private|protected|public|static|yield") and
      not exists(DotExpr de | id = de.getProperty()) and
      not exists(Property prop | id = prop.getNameExpr()) and
      // exclude JSX attribute names
      not exists(JSXElement e | id = e.getAnAttribute().getNameExpr())
select id, "Identifier name is a reserved word."