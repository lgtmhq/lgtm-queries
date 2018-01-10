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
 * @name Confusing method names because of capitalization
 * @description Methods in the same class whose names differ only in capitalization are
 *              confusing.
 * @kind problem
 * @problem.severity recommendation
 * @precision very-high
 * @id java/confusing-method-name
 * @tags maintainability
 *       readability
 *       naming
 */
import java

from Method m, Method n
where m.getDeclaringType() = n.getDeclaringType() and
      m.getName().toLowerCase() = n.getName().toLowerCase() and
      not m.getAnAnnotation() instanceof DeprecatedAnnotation and
      not n.getAnAnnotation() instanceof DeprecatedAnnotation and
      m.getName() < n.getName()
select m, "The method '" + m.getName() + "' may be confused with $@.", n, n.getName()
