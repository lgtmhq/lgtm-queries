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
 * @name Thread-unsafe use of DateFormat
 * @description Static fields of type 'DateFormat' (or its descendants) should be avoided
 *              because the class 'DateFormat' is not thread-safe.
 * @kind problem
 * @problem.severity warning
 */
import default

from Field f, Class dateFormat
where f.isStatic() and 
      f.isFinal() and 
      (f.isPublic() or f.isProtected()) and
      dateFormat.hasQualifiedName("java.text", "DateFormat") and
      f.getType().(RefType).hasSupertype*(dateFormat) and
      exists(MethodAccess m | m.getQualifier().(VarAccess).getVariable() = f)
select f, "Found static field of type " + f.getType().getName() + " in " 
                                        + f.getDeclaringType().getName() + "."
