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
 * @name Setter ignores its parameter
 * @description A setter function can silently ignore the new value that the property is meant to
 *              be set to, but this may result in unexpected behavior and could indicate a bug.
 * @kind problem
 * @problem.severity recommendation
 * @id js/ignored-setter-parameter
 * @tags reliability
 *       maintainability
 *       language-features
 * @precision high
 */

import javascript
import semmle.javascript.RestrictedLocations

from PropertySetter s, FunctionExpr f, SimpleParameter p
where f = s.getInit() and
      p = f.getAParameter() and
      not exists (p.getVariable().getAnAccess()) and
      not f.usesArgumentsObject() and
      // the setter body is either empty, or it is not just a single 'throw' statement
      (not exists(f.getABodyStmt()) or
       exists (Stmt stmt | stmt = f.getABodyStmt() | not stmt instanceof ThrowStmt))
select (FirstLineOf)s, "This setter function does not use its parameter $@.", p, p.getName()