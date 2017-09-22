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
 * @name Unused local variable
 * @description A local variable that is never called or accessed may be an
 *              indication that the code is incomplete or has a typo.
 * @kind problem
 * @problem.severity recommendation
 * @precision high
 * @tags maintainability
 *       useless-code
 *       external/cwe/cwe-563
 */
import default

/**
 * A type that contains a template parameter type
 * (doesn't count pointers or references).
 * 
 * These types may have a constructor / destructor when they are
 * instantiated, that is not visible in their template form.
 *
 * Such types include template parameters, classes with a member variable
 * of template parameter type, and classes that derive from other such
 * classes. 
 */
class TemplateDependentType extends Type {
  TemplateDependentType() {
    this instanceof TemplateParameter or
    exists(TemplateDependentType t |
      this.refersToDirectly(t) and
      not this instanceof PointerType and
      not this instanceof ReferenceType
    )
  }
}

/**
 * A variable whose declaration has, or may have, side effects.
 */
predicate declarationHasSideEffects(Variable v) {
  exists (Class c | c = v.getType().getUnderlyingType().getUnspecifiedType() |
    c.hasConstructor() or
    c.hasDestructor()
  ) or
  v.getType() instanceof TemplateDependentType // may have a constructor/destructor
}

from LocalVariable v, Function f
where f = v.getFunction()
     and not exists(v.getAnAccess())
     and not v.isConst() // workaround for folded constants
     and not exists(DeclStmt ds | ds.getADeclaration() = v and ds.isInMacroExpansion()) // variable declared in a macro expansion 
     and not declarationHasSideEffects(v)
     and not exists(AsmStmt s | f = s.getEnclosingFunction())
     and not v.getAnAttribute().getName() = "unused"
     and not any(ErrorExpr e).getEnclosingFunction() = f // unextracted expr likely used `v`
select v, "Variable " + v.getName() + " is not used"
