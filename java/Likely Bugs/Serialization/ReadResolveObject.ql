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
 * @name ReadResolve must have Object return type, not void
 * @description An implementation of 'readResolve' that does not have the signature that is expected
 *              by the Java serialization framework is not recognized by the serialization
 *              mechanism.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @id java/wrong-readresolve-signature
 * @tags reliability
 *       maintainability
 *       language-features
 */
import java

from TypeSerializable serializable, Class c, Method m
where c.hasSupertype+(serializable) and
      m.getDeclaringType() = c and
      m.hasName("readResolve") and
      m.hasNoParameters() and
      not m.getReturnType() instanceof TypeObject
select m, "The method " + m.getName() 
          + " must be declared with a return type of Object rather than " 
          + m.getReturnType().getName() + "."
