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
 * @name Missing Override annotation
 * @description A method that overrides a method in a superclass but does not have an 'Override'
 *              annotation cannot take advantage of compiler checks, and makes code less readable.
 * @kind problem
 * @problem.severity recommendation
 * @precision high
 * @id java/missing-override-annotation
 * @tags maintainability
 */
import java

class OverridingMethod extends Method {
  OverridingMethod() {
    exists(Method m | this.overrides(m))
  }

  predicate isOverrideAnnotated() {
    this.getAnAnnotation() instanceof OverrideAnnotation
  }
}

from OverridingMethod m, Method overridden
where m.fromSource()
  and m.overrides(overridden)
  and not m.isOverrideAnnotated()
  and not exists(FunctionalExpr mref | mref.asMethod() = m)
select m, "This method overrides $@; it is advisable to add an Override annotation.",
  overridden, overridden.getDeclaringType() + "." + overridden.getName()
