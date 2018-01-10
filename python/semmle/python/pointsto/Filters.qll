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

/** Helper predicates for standard tests in Python commonly
 * used to filter objects by value or by type.
 */


import python
import semmle.dataflow.SSA

/** Holds if `c` is a call to `hasattr(obj, attr)`. */
predicate hasattr(CallNode c, ControlFlowNode obj, string attr) {
    c.getFunction().getNode().(Name).getId() = "hasattr" and
    c.getArg(0) = obj and
    c.getArg(1).getNode().(StrConst).getText() = attr
}

/** Holds if `c` is a call to `callable(obj)`. */
predicate is_callable(CallNode c, ControlFlowNode obj) {
    c.getFunction().(NameNode).getId() = "callable" and
    obj = c.getArg(0)
}

/** Holds if `c` is a call to `isinstance(use, cls)`. */
predicate isinstance(CallNode fc, ControlFlowNode cls, ControlFlowNode use) {
    fc.getFunction().(NameNode).getId() = "isinstance" and
    cls = fc.getArg(1) and fc.getArg(0) = use
}

/** Holds if `c` is a test comparing `x` and `y`. `is` is true if the operator is `is` or `==`, it is false if the operator is `is not` or `!=`. */
predicate equality_test(CompareNode c, ControlFlowNode x, boolean is, ControlFlowNode y) {
    exists(Cmpop op |
        c.operands(x, op, y) or
        c.operands(y, op, x)
        |
        (is = true and op instanceof Is or
         is = false and op instanceof IsNot or
         is = true and op instanceof Eq or
         is = false and op instanceof NotEq
        )
    )
}

/** Holds if `c` is a call to `issubclass(use, cls)`. */
predicate issubclass(CallNode fc, ControlFlowNode cls, ControlFlowNode use) {
    fc.getFunction().(NameNode).getId() = "issubclass" and
    fc.getArg(0) = use and cls = fc.getArg(1)
}

