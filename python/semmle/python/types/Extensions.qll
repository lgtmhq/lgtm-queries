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

import python


abstract class CustomPointsToFact extends @py_flow_node {

    string toString() { none() }

    abstract predicate pointsTo(Object value, ClassObject cls, ControlFlowNode origin);

}

abstract class CustomPointsToOriginFact extends CustomPointsToFact {

    string toString() { none() }

    abstract predicate pointsTo(Object value, ClassObject cls);

    predicate pointsTo(Object value, ClassObject cls, ControlFlowNode origin) {
        this.pointsTo(value, cls) and origin = this
    }

}

/* Examples */

/** The kwargs parameter (**kwargs) in a function definition is always a dict */
class KwArgsFact extends CustomPointsToOriginFact {

    KwArgsFact() {
        exists(Function f | f.getKwarg() = this.(ControlFlowNode).getNode()) 
    }

    predicate pointsTo(Object value, ClassObject cls) {
        value = this and
        cls = theDictType()
    }

}

/** The varargs (*varargs) in a function definition is always a tuple */
class VarargFact extends CustomPointsToOriginFact {

    VarargFact() {
        exists(Function f | f.getVararg() = this.(ControlFlowNode).getNode()) 
    }

    predicate pointsTo(Object value, ClassObject cls) {
        value = this and
        cls = theTupleType()
    }

}

/* A more complex example */

/** Any variable iterating over range or xrange must be an integer */
class RangeIterationVariableFact extends CustomPointsToOriginFact {

    RangeIterationVariableFact() {
        exists(For f, ControlFlowNode iterable |
            iterable.getBasicBlock().dominates(this.(ControlFlowNode).getBasicBlock()) and
            f.getIter().getAFlowNode() = iterable and
            f.getTarget().getAFlowNode() = this and
            iterable.refersTo(_, theRangeType(), _)
        )
    }

    predicate pointsTo(Object value, ClassObject cls) {
        value = this and
        cls = theIntType()
    }
}

