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
 * @name Serialization methods do not match required signature
 * @description A serialized class that implements 'readObject' or 'writeObject' but does not use
 *              the correct signatures causes the default serialization mechanism to be used.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @tags reliability
 *       maintainability
 *       language-features
 */
import java

from Method m, TypeSerializable serializable
where m.getDeclaringType().hasSupertype+(serializable) and
      m.getNumberOfParameters() = 1 and
      m.getAParameter().getType().(RefType).hasQualifiedName("java.io", "ObjectOutputStream") and
      (m.hasName("readObject") or m.hasName("writeObject")) and
      not m.isPrivate()
select m, "readObject and writeObject should be private methods."
