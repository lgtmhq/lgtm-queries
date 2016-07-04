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
import semmle.python.types.PointsTo

private predicate self_attribute_store_in_block(BasicBlock b, string attrname, ControlFlowNode stored) {
    exists(SsaVariable var |
       attribute_store(var, attrname, stored) and
       var.isSelf()
    ) and
    stored.getBasicBlock() = b
}

private predicate self_attribute_set_in_block(BasicBlock b, string attrname, ControlFlowNode stored) {
    self_attribute_store_in_block(b, attrname, stored)
    or
    self_attribute_set_in_block(b.getAPredecessor(), attrname, stored)
}

private predicate self_attribute_not_set_in_block(BasicBlock b, string attrname) {
    exists(BasicBlock other |
        b.getScope() = other.getScope() |
        self_attribute_set_in_block(other, attrname, _)
    )
    and
    not self_attribute_store_in_block(b, attrname, _)
    and
    (
        not self_attribute_set_in_block(b, attrname, _)
        or
        self_attribute_not_set_in_block(b.getAPredecessor(), attrname)
    )
}

predicate unconditionally_sets_self_attribute(FunctionObject method, string attrname) {
    forex(BasicBlock exit |
        exit.getLastNode() = method.getFunction().getANormalExit() |
        self_attribute_set_in_block(exit, attrname, _) and
        not self_attribute_not_set_in_block(exit, attrname)
    )
}

private predicate sets_self_attribute(FunctionObject method, string attrname, ControlFlowNode store) {
    exists(BasicBlock b |
        self_attribute_set_in_block(b, attrname, store) |
        b.getLastNode() = method.getFunction().getANormalExit()
    )
}

predicate call_sets_self_attribute(CallNode call, SsaVariable var, string attrname, ControlFlowNode store) {
    exists(FunctionObject method |
        /* `method` is called by `call` with `var` as the 'self' argument */
        self_method_call(call, var, method) and
        sets_self_attribute(method, attrname , store)
    )
}

private predicate self_method_call(CallNode call, SsaVariable var, FunctionObject method) {
    exists(FunctionObject caller, ClassObject cls, string name |
        self_param(var.getDefinition(), caller) |
        cls.lookupAttribute(_) = caller and
        call.getFunction().(AttrNode).getObject(name) = var.getAUse() and
        cls.lookupAttribute(name) = method
    )
}

predicate attribute_set_by_call(ControlFlowNode load, ControlFlowNode store) {
    exists(SsaVariable var, CallNode call, string attrname |
        /* `call` includes `store` to var.attr_name */
        call_sets_self_attribute(call, var, attrname, store) and
        attribute_load(load, var.getAUse(), attrname)
        |
        call.strictlyDominates(load)
    )
}

predicate attribute_store(SsaVariable var, string name, ControlFlowNode stored) {
    exists(AttrNode fstore |
        fstore.(DefinitionNode).getValue() = stored |
        fstore.isStore() and
        var.getAUse() = fstore.getObject(name)    
    )
    or
    exists(CallNode call |
        intermediate_points_to(call.getFunction(), builtin_object("setattr"), _) and
        var.getAUse() = call.getArg(0) and
        call.getArg(1).getNode().(StrConst).getText() = name and
        call.getArg(2) = stored
    )
}

/** A load of an attribute, either directly or through getattr,
 * `objectuse` is the use of the object with attribute `name`
 */
predicate attribute_load(ControlFlowNode load, ControlFlowNode objectuse, string name) {
    exists(AttrNode fload |
        fload = load |
        fload.isLoad() and
        objectuse = fload.getObject(name)
    )
    or
    exists(CallNode call |
        call = load |
        intermediate_points_to(call.getFunction(), builtin_object("getattr"), _) and
        objectuse = call.getArg(0) and
        call.getArg(1).getNode().(StrConst).getText() = name
    )
}
