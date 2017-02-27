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

/* Level 0 support */

predicate none_points_to(ControlFlowNode n, Object value, ClassObject cls, ControlFlowNode origin) { none() }

predicate none_failed_inference(ClassObject cls, string reason) { none() }

ClassObject none_class_base_type(ClassObject cls, int n) { none() }

predicate none_is_new_style(ClassObject cls) { none() }

predicate none_has_explicit_metaclass(ClassObject cls) { none() }

ClassObject none_get_a_super_type(ClassObject cls) { none() }

ClassObject none_class_explicit_metaclass(ClassObject cls) { none() }

int none_declaring_class_index(ClassObject cls, string name) { none() }

predicate none_mro_sparse(ClassObject cls, ClassObject sup, int index) { none() }

predicate none_callToClassMayNotReturnInstance(ClassObject cls) { none() }

ClassObject none_known_global_type(Object value) { none() }

predicate none_call_sets_self_attribute(CallNode call, SsaVariable var, string attrname, ControlFlowNode store) { none() }

predicate none_module_attribute_points_to(ModuleObject mod, string name, Object value, ClassObject cls, ObjectOrCfg origin) { none() }

predicate none_self_param(ControlFlowNode self, FunctionObject func) { none() }

predicate none_py_module_attributes_explicit(Module m, string name, Object obj, ClassObject cls, ControlFlowNode origin) { none() }

predicate none_prohibited_class(ControlFlowNode f, ClassObject cls) { none() }

predicate none_prohibited_value(ControlFlowNode f, Object value) { none() }

predicate none_prohibited_class_on_edge(SsaVariable var, BasicBlock pred, BasicBlock succ, ClassObject cls) { none() }

predicate none_prohibited_value_on_edge(SsaVariable var, BasicBlock pred, BasicBlock succ, Object val) { none() }

predicate none_depth_first_indexed(ClassObject cls, ClassObject sup, int index) { none() }

predicate none_scope_defines_name(Scope scope, string name) { 
    exists(SsaVariable var | name = var.getId() and var.getAUse() = scope.getANormalExit())
}

ClassObject none_get_mro_item(ClassObject cls, int index) { none() }

predicate none_pruned(ControlFlowNode f) { none() }

predicate none_call_to_type(CallNode f) { none() }

predicate none_instantiation(CallNode f, ClassObject cls) { none() }

predicate none_attribute_store(SsaVariable var, string name, ControlFlowNode stored) { none() }

predicate none_attribute_load(ControlFlowNode load, ControlFlowNode objectuse, string name) { none() }

predicate none_ssa_variable_points_to(SsaVariable var, Object value, ClassObject cls, ControlFlowNode origin) { none() }

predicate none_module_exports(Module m, string name) { none() }

predicate none_six_add_metaclass(CallNode decorator_call, ClassObject decorated, ControlFlowNode metaclass) { none() }

class NoneCustomPointsFact extends @py_flow_node {

    string toString() { none() }

    predicate pointsTo(Object value, ClassObject cls, ControlFlowNode origin) {
        none()
    }

}

predicate none_call_not_understood(CallNode f) { any() }

predicate none_call_to_type_known_class(CallNode f, ClassObject cls) { none() }

predicate none_instantiation_regular_class(CallNode f) { none() }

predicate none_call_to_builtin_function_known_return_type(CallNode f) { none() }

predicate none_instance_attribute_store(ClassObject owning_class, string attr_name, Object value, ClassObject cls, ControlFlowNode origin) { none() }

predicate none_class_lookup_in_mro(ClassObject cls, ClassObject start, string name, Object object) { none() }

predicate none_function_never_returns(FunctionObject func) { none() }

class NonePointsToFilter extends ConditionalControlFlowNode {

    NonePointsToFilter() {
        none()
    }

    boolean isTrueFor(ControlledVariable var) { none() }

    boolean isTrueForAttribute(SsaVariable var, string attr_name) { none() }

    predicate allowedValue(ControlledVariable var, Object value) { none() }

    predicate allowedClass(ClassObject cls) { none() }

    ControlFlowNode getRelevantUse(ControlledVariable var) { none() }

}

predicate none_method_called_from_init(FunctionObject method, ClassObject owner) { none() }

predicate none_class_attribute_lookup(ClassObject cls, string name, Object value, ClassObject vcls, ObjectOrCfg origin) { none() }

predicate none_import_star_defines_name(Scope s, string name) { none() }

FunctionObject none_get_a_callee(Scope caller) { none() }

SsaVariable none_global_in_non_import_time_scope(NameNode n) { none() }

predicate none_scope_precedes(Scope pre, Scope post) { none() }

CallNode none_get_a_call(FunctionObject func) { none() }

predicate none_global_use_points_to(NameNode n, Object value, ClassObject cls, ControlFlowNode origin) { none() }

ControlFlowNode none_get_global_ssa_defn_at_scope_end_candidate(GlobalVariable v, Scope f) { none() }

ClassObject none_get_an_improper_super_type(ClassObject cls) { none() }

predicate none_attribute_store_load_pair(ControlFlowNode stored_value, ControlFlowNode load) { none() }

predicate none_abstract_class(ClassObject cls) { none() }

predicate none_global_ssa_defn(GlobalVariable v, ControlFlowNode node, string kind) { none() }
