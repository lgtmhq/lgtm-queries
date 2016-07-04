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
 * Combined points-to and type-inference for "run-time" (as opposed to "import-time" values)
 * The main relation runtime_points_to(node, object, cls, origin) relates a control flow node
 * to the possible objects it points-to the inferred types of those objects and the 'origin'
 * of those objects. The 'origin' is the point in source code that the object can be traced
 * back to. To handle the case where the class of an object cannot be inferred, but so that
 * we can track the object regardless, a special object "theUnknownType()" is used.
 */
import python
import Extensions
private import Attributes

private predicate original_values(ControlFlowNode f, Object value) {
    (
        value = f.getNode().(ImmutableLiteral).getLiteralObject()
        or
        f.isLiteral() and value = f and not f.getNode() instanceof ImmutableLiteral
        or
        f.isClass() and value = f
        or
        f.isFunction() and value = f
    )
}

private predicate original_unknowns(ControlFlowNode f, Object value) {
    (
        f.getNode() instanceof BinaryExpr
        or
        f.getNode() instanceof UnaryExpr
        or
        f.getNode() instanceof BoolExpr
        or
        f.getNode() instanceof Compare
        or
        f.isParameter()
    ) and value = f
}

/** INTERNAL -- Use n.refersTo(value, _, origin) instead */
cached predicate intermediate_points_to(ControlFlowNode n, Object value, ControlFlowNode origin) {
    /* Extend import-time analysis, regardless of scope.
     * This exists to avoid negative recursion.
     */
    original_values(n, value) and origin = n
    or
    module_level_points_to(n, value, origin)
    or
    builtin_points_to(n, value, origin)
    or
    import_time_points_to(n, value, origin)
    or
    exists(string attr_name, ModuleObject mod | 
        intermediate_points_to(n.(AttrNode).getObject(attr_name), mod, _) and
        mod.attributeRefersTo(attr_name, value, origin)
    )
    or
    intermediate_import_points_to(n, value, origin)
    or
    intermediate_from_import_points_to(n, value, origin)
}

private predicate intermediate_import_points_to(ControlFlowNode f, ModuleObject value, ControlFlowNode origin) {
    exists(string name, ImportExpr i | 
        i.getAFlowNode() = f and i.getImportedModuleName() = name and
        value.importedAs(name) |
        value.isC() and origin = f
        or
        not value.isC() and origin = value.getModule().getEntryNode()
    )
}

private predicate intermediate_from_import_points_to(ImportMemberNode f, Object value, ControlFlowNode origin) {
    /* Two options here:
     * 1. We can infer the module's attribute, and that attribute has an origin
     * 2. We can infer the module's attribute, but the attribute has no origin
     */
    exists(ImportMember im, string name |
        im.getAFlowNode() = f and name = im.getName() |
        exists(ModuleObject module | 
            intermediate_points_to(f.getModule(name), module, _) |
            module.attributeRefersTo(name, value, origin) /* 1. */
            or
            not module.attributeRefersTo(name, _, _) and /* 2. */
            value = module.getAttribute(name) and origin = f
        )
    )
    and
    /* If locally defined in init, then defer to import time points to */
    not is_locally_defined_from_dot_import_in_init(f, _)
}

/** Whether there is a condition somewhere that controls whether 'var' may (or must not, depending on 'parity') 
 * hold a value of class 'cls' on the edge from 'pred' to 'succ'.
*/
private predicate controlled_class(ControlFlowNode f, ClassObject cls, boolean parity) {
    exists(ConditionOnVariable cond | 
        cls = allowed_class(cond) and
        cond.appliesTo(f, parity)
    )
}

/** Get the class(es) that the condition allows */
private ClassObject allowed_class(ConditionOnVariable cond) {
    /* Instances of a class */
    exists(IsInstance isi, Object cls_or_tuple, ClassObject scls |
        scls = result.getAnImproperSuperType() and
        isi = cond and
        intermediate_points_to(isi.getClass(), cls_or_tuple, _) |
        /* cls_or_tuple is a class */
        cls_or_tuple = scls
        or
        intermediate_points_to(cls_or_tuple.(TupleNode).getElement(_), scls, _)
    )
    or
    /* Is a callable */
    cond instanceof IsCallable  and result.isCallable()
    or
    /* hasattr(...) */
    exists(string attr |
        cond.(HasAttr).getAttr() = attr and
        result.hasAttribute(attr)
    )
}

/** Whether there is a condition somewhere that controls whether 'var' may not hold 'value' on the 
 * edge from 'pred' to 'succ'.
*/
private predicate prohibited_value(ControlFlowNode f, Object value) {
    exists(ConditionOnVariable cond |
        cond.appliesTo(f, false) and
        value = allowed_value(cond)
    )
}

/** Whether there is a condition somewhere that controls whether 'var' may not hold a value of class 'cls' on the 
 * edge from 'pred' to 'succ'.
 */
pragma[inline] private predicate prohibited_value_on_edge(SsaVariable var, BasicBlock pred, BasicBlock succ, Object value) {
    exists(ConditionOnVariable cond |
        cond.controlsEdge(var, pred, succ, false) and value = allowed_value(cond)
        or
        cond.controlsEdge(var, pred, succ, true) and not value = allowed_value(cond) and
        exists(allowed_value(cond)) and unique_object(value)
    )
}

/** Whether there is a (almost certain) one-to-one relation between Python runtime object and database entity.
 * This is true for all numeric objects, True, False, None and classes.
 */
private predicate unique_object(Object value) {
    value instanceof NumericObject or
    value instanceof ClassObject or
    value = theNoneObject() or
    value = theTrueObject() or value = theFalseObject()
}

/** Get the values(es) that the condition allows */
private Object allowed_value(ConditionOnVariable cond) {
    /* Subclasses of a class */
    exists(IsSubclass iss, ClassObject scls |
        iss = cond and
        intermediate_points_to(iss.getClass(), scls, _) |
        result.(ClassObject).getAnImproperSuperType() = scls
    )
    or
    exists(IsEqual iseq |
        iseq = cond |
        intermediate_points_to(iseq.getObject(), result, _)
    )
}

/** Whether there is a condition somewhere that controls whether 'var' may hold a value of class 'cls' on the 
 * edge from 'pred' to 'succ'.
 */
private predicate required_class_on_edge(SsaVariable var, BasicBlock pred, BasicBlock succ, ClassObject cls) {
    exists(ConditionOnVariable cond |
        cond.controlsEdge(var, pred, succ, true) and cls = allowed_class(cond)
    )
}

/** Whether there is a condition somewhere that controls whether 'var' may not hold a value of class 'cls' on the 
 * edge from 'pred' to 'succ'.
 */
private predicate prohibited_class_on_edge(SsaVariable var, BasicBlock pred, BasicBlock succ, ClassObject cls) {
    exists(ConditionOnVariable cond |
        cond.controlsEdge(var, pred, succ, false) and cls = allowed_class(cond)
    )
}

/** Whether f is a use of a variable and the value of that use must be tf */
private predicate must_have_boolean_value(ControlFlowNode f, boolean tf) {
    exists(IsTrue ist | ist.appliesTo(f, tf))
}

/** Whether f is a use of a variable and the value of that use must be tf */
private predicate must_have_boolean_value_on_edge(SsaVariable var, BasicBlock pred, BasicBlock succ, boolean tf) {
    exists(IsTrue ist |
        ist.controlsEdge(var, pred, succ, tf)
    )
}

/** INTERNAL -- Use f.refersTo(value, cls, origin) instead */
cached predicate runtime_points_to(ControlFlowNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    original_unknowns(f, value) and origin = f and cls = theUnknownType()
    or
    intermediate_points_to(f, value, origin) and cls = global_type(value)
    or
    attribute_points_to(f, value, cls, origin)
    or
    if_exp_points_to(f, value, cls, origin)
    or
    import_points_to(f, value, origin) and cls = theModuleType()
    or
    from_import_points_to(f, value, cls, origin)
    or
    use_points_to(f, value, cls, origin)
    or
    def_points_to(f, value, cls, origin)
    or
    subscript_points_to(f, value, cls, origin) 
    or
    call_points_to(f, value, cls, origin)
    or
    nonlocal_variable_points_to(f, value, cls, origin)
    or
    f.(CustomPointsToFact).pointsTo(value, cls, origin)
}

/** A call to type() with a single argument */
private predicate call_to_type(CallNode f) {
    intermediate_points_to(f.getFunction(), theTypeType(), _) and not exists(f.getArg(1))
}

/** Whether a call to this class may not return an instance of this class. */
private predicate callToClassMayNotReturnInstance(ClassObject cls) {
    /* Django does this, so we need to account for it */
    cls.assignedInInit("__class__")
    or
    exists(ClassObject s | s = cls.getAnImproperSuperType() |
        /* Most builtin types "declare" __new__, such as `int`, yet are well behaved. */
        not s.isC() and s.declaresAttribute("__new__")
    )
}
  

/** Instantiation of an object */
private predicate instantiation(CallNode f, ClassObject cls) {
    intermediate_points_to(f.getFunction(), cls, _) and
    not call_to_type(f) and
    not callToClassMayNotReturnInstance(cls)
}

/** A call, including calls to type(arg), functions and classes */ 
private predicate call_points_to(CallNode f, Object value, ClassObject cls, ControlFlowNode origin) {
   /* There are six possibilities (that we currently account for) here.
    * 1. `type(known_type)` where we know the class of `known_type` and we know its origin
    * 2. `type(known_type)` where we know the class of `known_type`, 
    *        but we don't know it origin (because its a builtin type)
    * 3. `type(other)` where we don't know the type of `other
    * 4. `Class(...)` where Class is any class except type (with one argument).
    * 5. `func(...)` where we know the return type of func (becaue it is a builtin function)
    * 6. `func(...)` where we don't know the return type of func
    */ 
    (
        call_to_type(f) and
        runtime_points_to(f.getArg(0), _, value, _) and
        not value = theUnknownType() and
        cls = global_type(value) and
        (
            origin = value /* 1 */
            or
            origin = f and not exists(value.getOrigin()) /* 2 */
        )
    )
    or
    (    /* 3 */
        call_to_type(f) and
        runtime_points_to(f.getArg(0), _, theUnknownType(), _) and
        origin = f and value = f and cls = theUnknownType()
    )    
    or /* 4 */
    runtime_points_to(f.getFunction(), cls, _, _) and not call_to_type(f) and not callToClassMayNotReturnInstance(cls) and f = origin and value = f
    or /* 5 */   
    exists(BuiltinFunctionObject b |
        intermediate_points_to(f.getFunction(), b, _) and
        f = origin and value = f and
        cls = b.getAReturnType()
    )
    or
    (   /* 6 */
        not call_to_type(f) and not instantiation(f, _) and
        not exists(BuiltinFunctionObject b | 
            intermediate_points_to(f.getFunction(), b, _) and
            exists(b.getAReturnType())
        ) and
        /* Avoid having two differing values for `getattr(obj, 'name')` */
        not attribute_load(f, _, _) and
        f = origin and value = f and cls = theUnknownType()
    )
}

private predicate attribute_points_to(ControlFlowNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    exists(SsaVariable var, ControlFlowNode stored, string name |
        /* Is there a local store to the same attribute of the same SSA variable which dominates this use? */
        attribute_store(var, name, stored) and
        attribute_load(f, var.getAUse(), name) and
        runtime_points_to(stored, value, cls, origin) and
        stored.strictlyDominates(f) and
        not exists(CallNode call |
            call_sets_self_attribute(call, var, name, _) and
            stored.strictlyDominates(call) and
            call.strictlyDominates(f)
        )
    )
    or
    exists(ControlFlowNode stored |
        attribute_set_by_call(f, stored) |
        runtime_points_to(stored, value, cls, origin)
    )
    or
    class_attribute_lookup(f, value, origin) and cls = global_type(value)
    or
    module_attribute_lookup(f, value, origin) and cls = global_type(value)
    or
    instance_attribute_points_to(f, value, cls, origin)
}

private predicate class_attribute_lookup(AttrNode f, Object value, ControlFlowNode origin) {
    f.isLoad() and
    exists(ControlFlowNode fval, string name |
        fval = f.getObject(name) |
        exists(ClassObject obj |
            runtime_points_to(fval, obj, _, _) |
            obj.attributeRefersTo(name, value, origin)
            or
            not obj.attributeRefersTo(name, _, _)  and
            value = obj.lookupAttribute(name) and origin = f
        )
    )
}

private predicate module_attribute_lookup(AttrNode f, Object value, ControlFlowNode origin) {
    f.isLoad() and
    exists(ControlFlowNode fval, string name |
        fval = f.getObject(name) |
        exists(ModuleObject obj |
            runtime_points_to(fval, obj, _, _) |
            obj.attributeRefersTo(name, value, origin)
            or
            not obj.attributeRefersTo(name, _, _) and
            value = obj.getAttribute(name) and origin = f
        )
    )
}

/* Manual join ordering */
private predicate instance_attribute_points_to_candidate(ControlFlowNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    /* `f` is `x.attr_name` where `x` is an instance of `self_class` */
    exists(ClassObject self_class, string attr_name |
        /* `f` is `x.attr_name` where `x` is an instance of `self_class` */
        instance_attribute_store(self_class, attr_name, value, cls, origin) |
        exists(ControlFlowNode object |
            attribute_load(f, object, attr_name) and
            runtime_points_to(object, _, self_class, _)
        )
    )
}

private predicate instance_attribute_points_to(ControlFlowNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    instance_attribute_points_to_candidate(f, value, cls, origin) and
    not prohibited_class(f, cls) and
    not prohibited_value(f, value) and
    not must_have_boolean_value(f, value.booleanValue().booleanNot()) and
    // not locally redefined, unless this use dominates the redefinition
    not exists(SsaVariable var, ControlFlowNode stored, string name |
        attribute_store(var, name, stored) and
        attribute_load(f, var.getAUse(), name) and
        not f.strictlyDominates(stored)
    )
}

/** Helper for instance_attribute_points_to.
 *  Whether the `__init__` method of `owning_class`, or any method unconditionally called by it, contains an assignment:
 * `self.attr_name = value` or `setattr(self, 'attr_name', value)
 */
private predicate instance_attribute_store(ClassObject owning_class, string attr_name, Object value, ClassObject cls, ControlFlowNode origin) {
    exists(FunctionObject init, ControlFlowNode stored_value, SsaVariable var |
        method_called_from_init(init, owning_class) and
        stored_value.getScope() = init.getFunction() and
        attribute_store(var, attr_name, stored_value) and
        runtime_ssa_variable_points_to(var, _, owning_class, _) and
        runtime_points_to(stored_value, value, cls, origin)
    )
}

private predicate method_called_from_init(FunctionObject method, ClassObject owner) {
    owner.lookupAttribute("__init__") = method
    or
    exists(FunctionObject caller, CallNode call |
        method_called_from_init(caller, owner) and
        call.getScope() = caller.getFunction() and
        dominates_all_normal_exits(call) |
        exists(ControlFlowNode self, AttrNode attr, string name, ClassObject mro_type |
            attr = call.getFunction() and
            is_self(self) and
            super_call(attr.getObject(name), self, mro_type) and
            method = owner.lookupMro(owner.nextInMro(mro_type), name)
        )
        or
        exists(AttrNode self_attr, string name |
            call.getFunction() = self_attr and
            is_self(self_attr.getObject(name)) |
            owner.lookupAttribute(name) = method
        )
    )
}

private predicate is_self(NameNode self) {
    self_param(self, _)
    or
    exists(SsaVariable self_var |
        self_param(self_var.getDefinition(), _) and
        self = self_var.getAUse()
    )
}

/** Does a call dominates all of the normal exits? 
 * This is a cheap, conservative approximation for "is a method called 
 * unconditionally, given that this function exits normally".
 * The exact version is just too slow.
 */
private predicate dominates_all_normal_exits(CallNode call) {
    exists(Function f |
        call.getScope() = f |
        forex(ControlFlowNode exit |
            f.getANormalExit() = exit |
            call.getBasicBlock().dominates(exit.getBasicBlock())
        )
    )
}


private predicate if_exp_points_to(IfExprNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    runtime_points_to(f.getAnOperand(), value, cls, origin)
}

private predicate import_points_to(ControlFlowNode f, ModuleObject value, ControlFlowNode origin) {
    exists(string name, ImportExpr i | 
        i.getAFlowNode() = f and i.getImportedModuleName() = name and
        value.importedAs(name) |
        value.isC() and origin = f
        or
        not value.isC() and origin = value.getModule().getEntryNode()
    )
}

private predicate from_import_points_to(ImportMemberNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    /* Three options here:
     * 1. We can infer the module's attribute, and that attribute has an origin
     * 2. We can infer the module's attribute, but the attribute has no origin
     * 3. We can't infer the module's attribute.
     */
    exists(ImportMember im, string name |
        im.getAFlowNode() = f and name = im.getName() |
        exists(ModuleObject module | 
            intermediate_points_to(f.getModule(name), module, _) |
            module.attributeRefersTo(name, value, origin) /* 1. */
            or
            not module.attributeRefersTo(name, _, _) and /* 2. */
            value = module.getAttribute(name) and origin = f
        )
        or
        not exists(ModuleObject module | /* 3. */
            intermediate_points_to(f.getModule(name), module, _) and
            exists(module.getAttribute(name))
        ) and f = origin and value = f
    )
    and cls = global_type(value) and
    /* If locally defined in init, then defer to import time points to */
    not is_locally_defined_from_dot_import_in_init(f, _)
}


/** Whether this variable is not bound. ie. free. */
private predicate not_bound(SsaVariable var) {
    not exists(var.getDefinition()) and not exists(var.getAPhiInput())
    or exists(SsaVariable phi | phi = var.getAPhiInput() | not_bound(phi))
}

pragma[inline] predicate prohibited_class(ControlFlowNode f, ClassObject cls) {
    not cls = theUnknownType() and
    controlled_class(f, _, _) and
    not controlled_class(f, cls, true)
}

/** Get an object pointed to by a use (of a variable) */
private predicate use_points_to(ControlFlowNode n, Object value, ClassObject cls, ControlFlowNode origin) {
    not prohibited_class(n, cls) and
    not prohibited_value(n, value) and
    not must_have_boolean_value(n, value.booleanValue().booleanNot()) and
    exists(SsaVariable var |
        var.getAUse() = n |
        runtime_ssa_variable_points_to(var, value, cls, origin)
    )
}

/** Gets an object pointed to by a use with a ssa variable.
 * Note this can be a local variable in a function or class or a global variable at module scope */
private predicate runtime_ssa_variable_points_to(SsaVariable var, Object value, ClassObject cls, ControlFlowNode origin) {
    runtime_points_to(var.getDefinition(), value, cls, origin) and not exists(var.getAPhiInput())
    or
    ssa_phi_points_to(var, value, cls, origin)
}

/** What the the SSA variable 'var' may point to, provided that it is a phi node, taking care to account 
 * for guards on the incoming edges. The points-to relation for an SSA phi-node is the union of its incoming 
 * SSA variables, excepting those values and classes that are explicitly guarded against.
 */
private predicate ssa_phi_points_to(SsaVariable var, Object value, ClassObject cls, ControlFlowNode origin) {
    exists(SsaVariable incoming, BasicBlock pred, BasicBlock succ |
        pred = var.getPredecessorBlockForPhiArgument(incoming) and succ = var.getDefinition().getBasicBlock() |
        not prohibited_class_on_edge(incoming, pred, succ, cls) and
        not prohibited_value_on_edge(incoming, pred, succ, value) and
        (required_class_on_edge(incoming, pred, succ, cls) or not required_class_on_edge(incoming, pred, succ, _) or cls = theUnknownType()) and
        not must_have_boolean_value_on_edge(incoming, pred, succ, value.booleanValue().booleanNot()) and
        runtime_ssa_variable_points_to(incoming, value, cls, origin)
    )
}

/** Gets an object pointed to by this definition */
private predicate def_points_to(ControlFlowNode n, Object value, ClassObject cls, ControlFlowNode origin) {
    runtime_points_to(n.(DefinitionNode).getValue(), value, cls, origin)
    or
    /* Default values for parameters */
    n.isParameter() and 
    exists(Parameter p | 
        p.asName().getAFlowNode() = n and 
        runtime_points_to(p.getDefault().getAFlowNode(), value, cls, origin) 
    )
    or
    /* General parameters, including those with defaults. */
    n.isParameter() and not self_param(n, _) and value = n and origin = n and cls = theUnknownType()
    or
    exists(FunctionObject meth | self_param(n, meth) and self_type(meth, cls)) and value = n and origin = n
}

/** Whether `self` is the 0th parameter of `func`, and `func` is a normal method */
predicate self_param(ControlFlowNode self, FunctionObject func) {
    self.isParameter() and
    func.isNormalMethod() and
    func.getFunction().getArg(0).asName().getAFlowNode() = self and
    // `func` is not called as a function in the scope in which it is declared,
    // since the class, of which `func` is to be a method, will not exist
    // at that point.
    not exists(CallNode call |
        call.getScope() = func.getFunction().getScope() |
        import_time_points_to(call.getFunction(), func, _)
    )
}

/** Whether `cls` is a possible class of self in `method` */
private predicate self_type(FunctionObject method, ClassObject cls) {
    /* Standard call */
    cls.lookupAttribute(_) = method
    or
    /* Call via super */
    exists(AttrNode attr, string name, ClassObject start_type |
        super_call_types(attr.getObject(name), cls, start_type) and
        cls.lookupMro(start_type, name) = method
    )
}

private predicate subscript_load_store_pair(SubscriptNode store, SubscriptNode load) {
    /* We assume that given `x[a] = o; ...; p = x[b]` then `p` points-to `o` if
     * `x` is the same SSA variable in both cases and both `a` and `b` can point to 
     * the same object.
     */
    store.isStore() and load.isLoad() and
    exists(SsaVariable var |
        store.getValue() = var.getAUse() and load.getValue() = var.getAUse() |
        store.strictlyReaches(load)
    )
    and exists(Object index |
        runtime_points_to(store.getIndex(), index, _, _) and
        runtime_points_to(load.getIndex(), index, _, _)
    )
}

/** Gets an object pointed to by this subscript load */
private predicate subscript_points_to(SubscriptNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    exists(SubscriptNode store |
        subscript_load_store_pair(store, f) |
        runtime_points_to(store.(DefinitionNode).getValue(), value, cls, origin)
    )
}

private predicate nonlocal_points_to_candidate(NameNode f) { 
    exists(Function inner, Function outer, Variable var |
        /* use of var in inner function */
        f.uses(var) and f.getScope() = inner and
        /* var's scope is the outer function and inner is defined within outer */
        var.getScope() = outer and inner.getScope().getScope*() = outer and
        /* Variable is not redefined in inner (or any other inner function) */
        forall(NameNode def | def.defines(var) | def.getScope() = outer) and
        /* There is no call to inner in outer (which might see the variables uninitialized) */
        not call_to_inner_function(inner, outer)
    )
}

private predicate call_to_inner_function(Function inner, Function outer) {
    exists(SsaVariable v |
        exists(CallNode c | 
            c.getFunction() =  v.getAUse() and
            c.getScope().getScope*() = outer
        )
        and
        exists(FunctionExpr func |
            func = v.getDefinition().(DefinitionNode).getValue().getNode() and
            func.getInnerScope() = inner and
            func.getScope() = outer
        )
    )
}

private predicate nonlocal_variable_points_to(NameNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    not prohibited_class(f, cls) and
    not prohibited_value(f, value) and
    not must_have_boolean_value(f, value.booleanValue().booleanNot()) and
    nonlocal_points_to_candidate(f) and
    (
        /* use points to the same as the SSA variables for var at the end of the function. */
        exists(SsaVariable ssa |
            ssa.getAUse() = f and
            /* There is no other SSA variable that succeeds ssa */
            not exists(SsaVariable succ | succ.getAPhiInput() = ssa) and
            runtime_ssa_variable_points_to(ssa, value, cls, origin)
        )
        or
        /* Variable is unused except in inner function, so no SSA variable is created */
        not exists(SsaVariable ssa | ssa.getAUse() = f) and
        exists(Variable v | f.uses(v) |
            strictcount(NameNode def | def.defines(v)) = 1 and
            exists(NameNode def | 
                def.defines(v) |
                runtime_points_to(def, value, cls, origin)
            )
        )
    )
}

/* Helpers for intermediate_points_to */

/** Get an object pointed to by use of a global variable in a nested scope points-to. */
private predicate module_level_points_to(NameNode n, Object value, ControlFlowNode origin) {
    exists(Scope s, GlobalVariable v | 
        s = n.getScope() and n.uses(v) and
        not s instanceof ImportTimeScope |
        s.getEnclosingModule().(ImportTimeScope).objectReachingExit(v.getId(), value, origin)
    )
}

/** Object pointed to by a use of a builtin (not a global or local) */
private predicate builtin_points_to(NameNode n, Object value, ControlFlowNode origin) {
    origin = n and
    exists(Scope s, GlobalVariable v | 
        s = n.getScope() and n.uses(v) and
        not s instanceof ImportTimeScope |
        not s.getEnclosingModule().(ImportTimeScope).definesName(v.getId()) and
        value = builtin_object(v.getId())
    )
}

/** Whether `call` is a call to super() with for an object of class `self_type`
 * and the `start` class in the MRO. E.g
 * For a call `super(T, self)`. 
 * `self_type` is `type(self)` and `start` is `T`
 * Handles both Python 2 style `super(T, self)` and Python 3 style `super()`.
 */
predicate super_call_types(CallNode call, ClassObject self_type, ClassObject start_type) {
    exists(ClassObject mro_type, ControlFlowNode self |
        start_type = self_type.nextInMro(mro_type) and
        super_call(call, self, mro_type) and
        runtime_points_to(self, _, self_type, _)
    )
}

private predicate super_call(CallNode call, ControlFlowNode self, ClassObject mro_type) {
    intermediate_points_to(call.getFunction(), theSuperType(), _) and
    (
        intermediate_points_to(call.getArg(0), mro_type, _) and
        self = call.getArg(1)
        or
        major_version() = 3 and
        not exists(call.getArg(0)) and
        exists(Function func |
            call.getScope() = func and
            /* Implicit class argument is lexically enclosing scope */ 
            func.getScope() = mro_type.getPyClass() and
            /* Implicit 'self' is the 0th parameter */
            self = func.getArg(0).asName().getAFlowNode()
        )
    )
}

private ClassObject global_type(Object value) {
    result = known_global_type(value)
    or
    not exists(known_global_type(value)) and result = theUnknownType()
}

/* Helper for global_type */
private ClassObject known_global_type(Object value) {
    result = value.simpleClass() and not value instanceof ClassObject
    or
    result = value.(ClassObject).getMetaClass()
    or
    instantiation(value, result)
}

/** INTERNAL -- Do not use */
ClassObject theUnknownType() {
    py_special_objects(result, "_semmle_unknown_type")
}
