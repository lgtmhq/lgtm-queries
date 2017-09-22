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
 * @name Large object passed by value
 * @description An object larger than 64 bytes is passed by value to a function. Passing large objects by value unnecessarily use up scarce stack space, increase the cost of calling a function and can be a security risk. Use a pointer to the object instead.
 * @kind problem
 * @problem.severity recommendation
 * @precision high
 * @tags efficiency
 *       readability
 */
import default

from Function f, Parameter p, int size
where f.getAParameter() = p
  and p.getType().getSize() = size
  and size > 64
  and not p.getType().getUnderlyingType() instanceof ArrayType
select p, "This parameter is " + size.toString() + " bytes - consider passing a pointer/reference instead."
