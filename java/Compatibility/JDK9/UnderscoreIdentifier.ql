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
 * @name Underscore used as identifier
 * @description Use of a single underscore character as an identifier
 *              results in a compiler error with Java source level 9 or later.
 * @kind problem
 * @problem.severity recommendation
 * @precision high
 * @id java/underscore-identifier
 */
import java

class IdentifierElement extends Element {
  IdentifierElement() {
    this instanceof CompilationUnit or
    this.(RefType).isSourceDeclaration() or
    this.(Callable).isSourceDeclaration() or
    this instanceof Variable
  }
}

from IdentifierElement e, string msg
where e.fromSource()
  and not e.(Constructor).isDefaultConstructor()
  and (
    e.getName() = "_" and
    msg = "."
    or
    e.(CompilationUnit).getPackage().getName().splitAt(".") = "_" and
    msg = " in package name '" + e.(CompilationUnit).getPackage().getName() + "'."
  )
select e, "Use of underscore as a one-character identifier" + msg
