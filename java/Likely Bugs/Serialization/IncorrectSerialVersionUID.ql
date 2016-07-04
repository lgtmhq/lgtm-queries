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
 * @name Incorrect serialVersionUID field
 * @description A 'serialVersionUID' field that is declared in a serializable class but is of the 
 *              wrong type cannot be used by the serialization framework.
 * @kind problem
 * @problem.severity warning
 */
import default

from Field f
where f.hasName("serialVersionUID") and 
      (   not f.isFinal()
       or not f.isStatic()
       or not f.getType().hasName("long")) and
      exists(TypeSerializable serializable | f.getDeclaringType().getASupertype+() = serializable)
select f, "serialVersionUID should be final, static, and of type long."
