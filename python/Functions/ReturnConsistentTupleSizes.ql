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
 * @name Returning tuples with varying lengths
 * @description A function that potentially returns tuples of different lengths may indicate a problem.
 * @kind problem
 * @tags reliability
 *       maintainability
 * @problem.severity recommendation
 * @sub-severity high
 * @precision high
 * @id py/mixed-tuple-returns
 */

import python

predicate returns_tuple_of_size(Function func, int size, AstNode origin) {
    exists(Return return, TupleObject val |
        return.getScope() = func and
        return.getValue().refersTo(val, origin) |
        size = val.getLength()
    )
}


from Function func, int s1, int s2, AstNode t1, AstNode t2
where
    returns_tuple_of_size(func, s1, t1) and
    returns_tuple_of_size(func, s2, t2) and
    s1 < s2
select func, func.getQualifiedName() + " returns $@ and $@.", t1, "tuple of size " + s1, t2, "tuple of size " + s2
