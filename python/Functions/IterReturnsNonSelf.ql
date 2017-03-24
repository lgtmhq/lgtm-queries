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
 * @name Iterator does not return self from __iter__ method
 * @description Iterator does not return self from __iter__ method, violating the iterator protocol.
 * @kind problem
 * @tags reliability
 *       correctness
 * @problem.severity error
 * @sub-severity low
 * @precision high
 */

import python

Function iter_method(ClassObject t) {
		result = ((FunctionObject)t.lookupAttribute("__iter__")).getFunction()
}

predicate is_self(Name value, Function f) {
	 value.getVariable() = ((Name)f.getArg(0)).getVariable()
}

predicate returns_non_self(Function f) {
		exists(f.getFallthroughNode())
		or
		exists(Return r | r.getScope() = f and not is_self(r.getValue(), f))
		or
		exists(Return r | r.getScope() = f and not exists(r.getValue()))
}

from ClassObject t, Function iter
where t.isIterator() and iter = iter_method(t) and returns_non_self(iter)
select t, "Class " + t.getName() + " is an iterator but its $@ method does not return 'self'.", iter, iter.getName()