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
 * @name Inconsistent method resolution order
 * @description Class definition will raise a type error at runtime due to inconsistent method resolution order(MRO)
 * @kind problem
 * @problem.severity error
 */

import python

ClassObject left_base(ClassObject type, ClassObject base) {
		exists(int i | i > 0 and type.getBaseType(i) = base and result = type.getBaseType(i-1))
}

predicate invalid_mro(ClassObject t, ClassObject left, ClassObject right) {
    t.isNewStyle() and
		left = left_base(t, right) and left = t.nextInMro(right)
}

from ClassObject t, ClassObject left, ClassObject right
where invalid_mro(t, left, right)
select t, "Construction of class " + t.getName() + " can fail due to invalid method resolution order(MRO) for bases $@ and $@.",
left, left.getName(), right, right.getName()
