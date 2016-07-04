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
 * @name __iter__ method returns a non-iterator
 * @description The '__iter__' method returns a non-iterator which, if used in a 'for' loop, would raise a 'TypeError'.
 * @kind problem
 * @problem.severity warning
 */

import python

FunctionObject iter_method(ClassObject t) {
		result = t.lookupAttribute("__iter__")
}

cached ClassObject return_type(FunctionObject f) {
    exists(ControlFlowNode n, Return ret |
        ret.getScope() = f.getFunction() and ret.getValue() = n.getNode() and
        n.refersTo(_, result, _)
    )
}

from ClassObject t, FunctionObject iter
where exists(ClassObject ret_t | iter = iter_method(t) and
          ret_t = return_type(iter) and
          not ret_t.isIterator()
      )

select iter, "The '__iter__' method of iterable class $@ does not return an iterator.", t, t.getName()
