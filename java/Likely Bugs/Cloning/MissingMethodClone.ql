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
 * @name No clone method
 * @description A class that implements 'Cloneable' but does not override the 'clone' method will
 *              have undesired behavior.
 * @kind problem
 * @problem.severity error
 * @precision medium
 * @tags reliability
 *       maintainability
 */
import java

from Class t, TypeCloneable cloneable
where t.hasSupertype+(cloneable) and
      not t.isAbstract() and
      not exists(CloneMethod m | t.getAMethod() = m) and
      exists(Field f | f.getDeclaringType() = t and not f.isStatic()) and
      t.fromSource()
select t, "No clone method, yet implements Cloneable."
