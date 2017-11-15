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
 * @name Ineffective parameter type
 * @description Omitting the name of a parameter causes its type annotation to be parsed as the name.
 * @kind problem
 * @problem.severity warning
 * @id js/ineffective-parameter-type
 * @precision high
 * @tags correctness
 *       typescript
 */

import javascript

/**
 * Holds if there is a predefined type of the given name, and a parameter
 * of that name is likely intended to be typed.
 */
predicate isCommonPredefinedTypeName(string name) {
  name = "string" or
  name = "number" or
  name = "boolean"
}

/**
 * Any local type declaration, excluding imported names that are not explicitly used as types.
 */
class DefiniteTypeDecl extends TypeDecl {
  DefiniteTypeDecl() {
    this = any(ImportSpecifier im).getLocal()
    implies
    exists(getLocalTypeName().getAnAccess())
  }
}

from SimpleParameter parameter, Function function, Locatable link, string linkText
where function.getFile().getFileType().isTypeScript()
  and function.getAParameter() = parameter
  and not function.hasBody()
  and not exists(parameter.getTypeAnnotation())
  and (
    isCommonPredefinedTypeName(parameter.getName()) and link = parameter and linkText = "predefined type '" + parameter.getName() + "'"
    or
    exists (DefiniteTypeDecl decl, LocalTypeName typename |
      decl = typename.getFirstDeclaration() and
      parameter.getVariable().getScope().getOuterScope*() = typename.getScope() and
      decl.getName() = parameter.getName() and
      link = decl and
      linkText = decl.describe())
  )
select parameter, "The parameter '" + parameter.getName() + "' has type 'any', but its name coincides with the $@.", link, linkText
