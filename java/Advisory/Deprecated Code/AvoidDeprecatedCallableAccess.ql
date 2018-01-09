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
 * @name Deprecated method or constructor invocation
 * @description Using a method or constructor that has been marked as deprecated may be dangerous or
 *              fail to take advantage of a better method or constructor.
 * @kind problem
 * @problem.severity recommendation
 * @precision high
 * @id java/deprecated-call
 * @tags changeability
 *       external/cwe/cwe-477
 */
import java

private
predicate isDeprecatedCallable(Callable c) {
  c.getAnAnnotation() instanceof DeprecatedAnnotation
  or exists(c.getDoc().getJavadoc().getATag("@deprecated"))
}

from Call ca, Callable c
where ca.getCallee() = c
  and isDeprecatedCallable(c)
  // Exclude deprecated calls from within deprecated code.
  and not isDeprecatedCallable(ca.getCaller())
select ca, "Invoking $@ should be avoided because it has been deprecated.",
  c, c.getDeclaringType() + "." + c.getName()
