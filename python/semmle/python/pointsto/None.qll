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

import python
import PointsToContext

/* Fake predicates so that This.qll behaves correctly in Studio */

module NonePointsTo {

    predicate points_to(ControlFlowNode n, int ctx, Object value, ClassObject cls, ControlFlowNode origin) { none() }

    CallNode get_a_call(FunctionObject func, int context) { none() }

    module Types {

        ClassObject get_an_improper_super_type(ClassObject cls) { none() }

        predicate class_has_attribute(ClassObject cls, string name) { none() }

        ClassObject class_base_type(ClassObject cls, int index) { none() }

        predicate is_new_style(ClassObject cls) { none() }

        predicate abstract_class(ClassObject cls) { none() }

        predicate six_add_metaclass(CallNode decorator_call, ClassObject decorated, ControlFlowNode metaclass) { none() }

    }

    boolean test_evaluates_boolean(ControlFlowNode expr, ControlFlowNode use, int context, Object val, ClassObject cls, ObjectOrCfg origin) { none() }

    module Layer {

        predicate pruned(ControlFlowNode f, int ctx) { none() }

        predicate prunedEdge(BasicBlock pred, BasicBlock succ, int ctx) { none() }

        predicate module_attribute_points_to(ControlFlowNode mod, string name, Object value, ClassObject cls, ObjectOrCfg origin) { none() }

        ClassObject class_get_meta_class_candidate(ClassObject cls) { none() }

        predicate ssa_variable_points_to(EssaVariable var, int ctx, Object value, ClassObject vcls, ObjectOrCfg origin) { none() }

    }
}
