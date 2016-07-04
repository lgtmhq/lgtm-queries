// Copyright 2016 Semmle Ltd.
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
 * @name Externalizable but no public no-argument constructor
 * @description A class that implements 'Externalizable' but does not have a public no-argument 
 *              constructor causes an 'InvalidClassException' to be thrown.
 * @kind problem
 * @problem.severity warning
 */
import default

from Class extern, Interface externalizable
where externalizable.hasQualifiedName("java.io", "Externalizable") and
      extern.hasSupertype+(externalizable) and
      not extern.isAbstract() and
      not exists(Constructor c | c = extern.getAConstructor() |
        c.hasNoParameters() and
        c.isPublic()
      )
select extern, "This class is Externalizable but has no public no-argument constructor."
