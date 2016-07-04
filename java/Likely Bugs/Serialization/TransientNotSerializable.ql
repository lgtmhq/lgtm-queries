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
 * @name Transient field in non-serializable class
 * @description Using the 'transient' field modifier in non-serializable classes has no effect.
 * @kind problem
 * @problem.severity recommendation
 */
import default

from TypeSerializable serializable, Class c, Field f
where not c.hasSupertype+(serializable) and 
      f.getDeclaringType() = c and 
      f.isTransient()
select f, "The field " + f.getName() + " is transient but " + c.getName() 
                       + " is not Serializable."
