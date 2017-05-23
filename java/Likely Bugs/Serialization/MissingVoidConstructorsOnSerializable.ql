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
 * @name Serializable but no void constructor
 * @description A non-serializable, immediate superclass of a serializable class that does not
 *              itself declare an accessible, no-argument constructor causes deserialization to
 *              fail.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @tags reliability
 *       maintainability
 *       language-features
 */
import java

from Class serial, Class nonserial, TypeSerializable serializable
where serial.hasSupertype(nonserial) and
      serial.hasSupertype+(serializable) and
      not nonserial.hasSupertype+(serializable) and
      not exists(Constructor c |
        c = nonserial.getSourceDeclaration().getAConstructor()
        and c.hasNoParameters()
        and not(c.isPrivate())
      ) and
      serial.fromSource()
select serial,
  "This class is serializable, but its non-serializable " +
  "super-class $@ does not declare a no-argument constructor.",
  nonserial, nonserial.getName()
