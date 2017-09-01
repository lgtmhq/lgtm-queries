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

/** This library allows custom extensions to the points-to analysis to incorporate
 * custom domain knowledge into the points-to analysis.
 * 
 * This should be considered an advance feature. Modifying the points-to analysis
 * can cause queries to give strange and misleading results, if not done with care.
 */

import python
private import semmle.python.pointsto.Penultimate
private import semmle.python.pointsto.PointsToContext

/* Custom Facts. This extension mechanism allows you to add custom
 * sources of data to the points-to analysis.
 */

abstract class FinalCustomPointsToFact extends @py_flow_node {

    string toString() { none() }

    abstract predicate pointsTo(FinalContext context, Object value, ClassObject cls, ControlFlowNode origin);

}

abstract class PenultimateCustomPointsToFact extends @py_flow_node {

    string toString() { none() }

    abstract predicate pointsTo(PenultimateContext context, Object value, ClassObject cls, ControlFlowNode origin);

}

class Layer0CustomPointsToFact extends @py_flow_node {

    string toString() { none() }

    predicate pointsTo(Layer0Context ctx, Object value, ClassObject cls, ControlFlowNode origin) {
        none()
    }

}

abstract class CustomPointsToFact extends FinalCustomPointsToFact {

}

abstract class CustomPointsToOriginFact extends FinalCustomPointsToFact {

    string toString() { none() }

    abstract predicate pointsTo(Object value, ClassObject cls);

    predicate pointsTo(FinalContext context, Object value, ClassObject cls, ControlFlowNode origin) {
        this.pointsTo(value, cls) and origin = this and context.appliesTo(this)
    }

}

/* An example */

/** Any variable iterating over range or xrange must be an integer */
class RangeIterationVariableFact extends FinalCustomPointsToFact {

    RangeIterationVariableFact() {
        exists(For f, ControlFlowNode iterable |
            iterable.getBasicBlock().dominates(this.(ControlFlowNode).getBasicBlock()) and
            f.getIter().getAFlowNode() = iterable and
            f.getTarget().getAFlowNode() = this and
            PenultimatePointsTo::points_to(iterable, _, theRangeType(), _, _)
        )
    }

    predicate pointsTo(FinalContext context, Object value, ClassObject cls, ControlFlowNode origin) {
        value = this and 
        origin = this and
        cls = theIntType() and
        context.appliesTo(this)
    }
}


