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
 * Combined points-to and type-inference.
 * The main relation penultimate_points_to(node, object, cls, origin) relates a control flow node
 * to the possible objects it points-to the inferred types of those objects and the 'origin'
 * of those objects. The 'origin' is the point in source code that the object can be traced
 * back to. To handle the case where the class of an object cannot be inferred, but so that
 * we can track the object regardless, a special object "theUnknownType()" is used.
 */
 
 /* Notes on the implementation
  * The ultimate goal of this library is to provide various final_xxx predicates
  * which are used as implementation of various "public" API predicates like 
  * ControlFlowNode.refersTo() and FunctionObject.getACall().
  * 
  * Predicates can be 
  * 1. Provide implementation for the API. QLdoc will contain "INTERNAL -- Use ... instead"
  * 2. Required to be public as they may be needed for custom points-to extensions.
  * 2. Provide predicate for the next layer up. Will be marked "INTERNAL -- Do not not use"
  * 4. Internal to a layer -- these are marked private
  *
  */

import python
private import Base
private import semmle.python.types.Extensions
private import Layer0

private ClassObject penultimate_global_type(Object value) {
    result = penultimate_known_global_type(value)
    or
    not exists(layer0_known_global_type(value)) and result = theUnknownType()
}


/* Helper for global_type */
/** INTERNAL -- Do not use */
ClassObject penultimate_known_global_type(Object value) {
    result = simple_types(value)
    or
    result = penultimate_class_get_meta_class(value)
    or
    penultimate_instantiation(value, result)
}

/** INTERNAL -- Do not not use */
pragma[inline]
predicate penultimate_prohibited_attribute(AttrNode f, Object value, ClassObject cls) {
    exists(Layer0PointsToFilter cond, SsaVariable var, string name |
        f.getObject(name) = var.getAUse() |
        cond.controlsAttribute(var, name, f.getBasicBlock(), true)
        and not cond.allowedValue(var.(ControlledVariable), value)
        and not cond.allowedClass(cls)
        or
        cond.controlsAttribute(var, name, f.getBasicBlock(), false) and cond.allowedValue(var.(ControlledVariable), value)
        or
        cond.controlsAttribute(var, name, f.getBasicBlock(), false) and cond.allowedClass(cls)
    )
}

/** INTERNAL -- Do not not use */
pragma[inline]
predicate penultimate_prohibited_use(NameNode f, Object value, ClassObject cls) {
    exists(Layer0PointsToFilter cond, ControlledVariable var |
        var.getAUse() = f |
        cond.controls(var, f.getBasicBlock(), true)
        and not cond.allowedValue(var.(ControlledVariable), value)
        and not cond.allowedClass(cls)
        or
        cond.controls(var, f.getBasicBlock(), false) and cond.allowedValue(var.(ControlledVariable), value)
        or
        cond.controls(var, f.getBasicBlock(), false) and cond.allowedClass(cls)
    )
}

/* Whether there is a condition somewhere that controls whether 'var' may not hold a value 'value' of class 'cls' on the 
 * edge from 'pred' to 'succ'.
 */
/** INTERNAL -- Do not not use */
pragma [inline]
predicate penultimate_prohibited_on_edge(ControlledVariable var, BasicBlock pred, BasicBlock succ, Object value, ClassObject cls) {
    exists(Layer0PointsToFilter cond |
        cond.controlsEdge(var, pred, succ, true)
        and not cond.allowedValue(var, value)
        and not cond.allowedClass(cls) 
        or
        cond.controlsEdge(var, pred, succ, false) and cond.allowedValue(var, value)
        or
        cond.controlsEdge(var, pred, succ, false) and cond.allowedClass(cls)
    )
}

private predicate penultimate_points_to_candidate(ControlFlowNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    kwargs_points_to(f, cls) and value = f and origin = f
    or
    varargs_points_to(f, cls) and value = f and origin = f
    or
    base_points_to(f, value, origin) and cls = penultimate_global_type(value)
    or
    penultimate_attribute_points_to(f, value, cls, origin)
    or
    penultimate_if_exp_points_to(f, value, cls, origin)
    or
    penultimate_import_points_to(f, value, origin) and cls = theModuleType()
    or
    penultimate_from_import_points_to(f, value, cls, origin)
    or
    penultimate_use_points_to(f, value, cls, origin)
    or
    penultimate_def_points_to(f, value, cls, origin)
    or
    penultimate_subscript_points_to(f, value, cls, origin) 
    or
    penultimate_call_points_to(f, value, cls, origin)
    or
    penultimate_sys_version_info_slice(f) and value = f and origin = f and cls = theTupleType()
    or
    penultimate_sys_version_info_index(f) and value = f and origin = f and cls = theIntType()
    or
    penultimate_six_metaclass_points_to(f, value, cls, origin)
    or
        f.(PenultimateCustomPointsToFact).pointsTo(value, cls, origin)
}

private predicate penultimate_six_metaclass_points_to(ControlFlowNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    exists(ControlFlowNode meta |
        layer0_six_add_metaclass(f, value, meta) and
        penultimate_points_to(meta, cls, _, _)
    ) and
    origin = value
}


/** INTERNAL -- Use f.refersTo(value, cls, origin) instead */
cached
predicate penultimate_points_to(ControlFlowNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    not layer0_pruned(f) and
    penultimate_points_to_candidate(f, value, cls, origin)
}

/* A call to type() with a single argument */
/** INTERNAL -- Do not use */
cached
predicate penultimate_call_to_type(CallNode f) {
    penultimate_points_to(f.getFunction(), theTypeType(), _, _) and not exists(f.getArg(1))
}

/* Whether a call to this class may not return an instance of this class. */
/** INTERNAL -- Do not not use */
predicate penultimate_callToClassMayNotReturnInstance(ClassObject cls) {
    /* Django does this, so we need to account for it */
    penultimate_assigned_in_init(cls, "__class__")
    or
    exists(ClassObject s | s = penultimate_get_an_improper_super_type(cls) |
        /* Most builtin types "declare" __new__, such as `int`, yet are well behaved. */
        not s.isC() and class_declares_attribute(s, "__new__")
    )
}

/** Instantiation of an object */
private predicate penultimate_instantiation(CallNode f, ClassObject cls) {
    penultimate_points_to(f.getFunction(), cls, _, _) and
    not layer0_call_to_type(f) and
    not layer0_callToClassMayNotReturnInstance(cls)
}


/* Call analysis logic
 * ===================
 *  There are seven possibilities (that we currently account for) here.
 * 1. `type(known_type)` where we know the class of `known_type` and we know its origin
 * 2. `type(known_type)` where we know the class of `known_type`, 
 *        but we don't know it origin (because its a builtin type)
 * 3. `type(other)` where we don't know the type of `other
 * 4. `Class(...)` where Class is any class except type (with one argument) and calls to that class return instances of that class
 * 5. `Class(...)` where Class is any class and calls to that class may return objects which are not instances of that class
 * 6. `func(...)` where we know the return type of func (because it is a builtin function)
 * 7. `func(...)` where we know the returned object and origin of func (because it is a Python function)
 * 8. `func(...)` where we don't know the return type of func
 */ 
private predicate call_to_type_points_to(CallNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    penultimate_call_to_type(f) and
    cls = theTypeType() and
    (
        penultimate_points_to(f.getArg(0), _, value, _) and
        not value = theUnknownType() and
        (origin.getNode() = value.getOrigin() or /* 1 */
         not exists(value.getOrigin()) and origin = f /* 2 */
        )
        or
        not exists(ClassObject argcls | /* 3 */
            layer0_points_to(f.getArg(0), _, argcls, _) and
            not argcls = theUnknownType()
        ) and
        value = f and
        origin = f
    )
}

/** INTERNAL -- Do not use */
predicate penultimate_call_not_understood(CallNode f) {
    penultimate_instantiation_irregular_class(f)
    or
    not penultimate_call_to_type(f) and
    not penultimate_instantiation(f, _) and
    not exists(BuiltinFunctionObject b | 
        penultimate_points_to(f.getFunction(), b, _, _) and
        exists(b.getAReturnType())
    ) and
    not penultimate_six_add_metaclass(f, _, _) and
    /* Avoid having two differing values for `getattr(obj, 'name')` */
    not penultimate_attribute_load(f, _, _) and
    not exists(PyFunctionObject func |
        f = penultimate_get_a_call(func)
    )
}

/** INTERNAL -- Do not use */
predicate penultimate_instantiation_regular_class(CallNode f) {
    exists(ClassObject maybe_cls |
        penultimate_points_to(f.getFunction(), maybe_cls, _, _) and
        not penultimate_callToClassMayNotReturnInstance(maybe_cls)
    )
}

private predicate penultimate_instantiation_irregular_class(CallNode f) {
    exists(ClassObject maybe_cls |
        penultimate_points_to(f.getFunction(), maybe_cls, _, _) and
        penultimate_callToClassMayNotReturnInstance(maybe_cls)
    )
}

private predicate penultimate_call_points_to_4(CallNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    not layer0_call_to_type(f) and
    layer0_instantiation_regular_class(f) and value = f and penultimate_points_to(f.getFunction(), cls, _, _) and origin = f
}

private predicate penultimate_call_points_to_6(CallNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    exists(BuiltinFunctionObject b |    
        penultimate_points_to(f.getFunction(), b, _, _) and
        cls = b.getAReturnType()
    ) and
    f = origin and value = f
}

private predicate penultimate_call_to_procedure_points_to(CallNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    exists(PyFunctionObject func |
        f = penultimate_get_a_call(func) and
        penultimate_implicitly_returns(func, value, cls) and origin.getNode() = func.getOrigin()
    )
}

private predicate penultimate_call_to_generator_points_to(CallNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    exists(PyFunctionObject func |
        f = penultimate_get_a_call(func) |
        func.getFunction().isGenerator() and origin = f and value = f and cls = theGeneratorType()
    )
}

private predicate penultimate_call_to_function_which_returns_argument_points_to(CallNode call, Object value, ClassObject cls, ControlFlowNode origin) {
   exists(PyFunctionObject func, int n |
        func.unconditionallyReturnsParameter(n) and
        penultimate_points_to(penultimate_get_positional_argument_for_call(func, call, n), value, cls, origin)
    )
}

private predicate penultimate_call_points_to_7(CallNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    exists(ControlFlowNode rval |
        exists(PyFunctionObject func |
            f = penultimate_get_a_call(func) and
            not func = layer0_six_add_metaclass_function() |
            rval = safe_return_node(func)
        ) and
        penultimate_points_to(rval, value, cls, origin)
    )
    and not is_parameter_default(origin)
}

/** A call, including calls to type(arg), functions and classes */
private predicate penultimate_call_points_to(CallNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    call_to_type_points_to(f, value, cls, origin)
    or
    penultimate_call_points_to_4(f, value, cls, origin)
    or
    penultimate_call_points_to_6(f, value, cls, origin)
    or
    /* Case 7a */
    penultimate_call_points_to_7(f, value, cls, origin)
    or
    /* Case 7b */
    penultimate_call_to_generator_points_to(f, value, cls, origin)
    or
    /* Case 7c */
    penultimate_call_to_function_which_returns_argument_points_to(f, value, cls, origin)
    or
    /* Case 7d */
    penultimate_call_to_procedure_points_to(f, value, cls, origin)
    or
    /* Cases 5 and 8 */
    layer0_call_not_understood(f) and value = f and cls = theUnknownType() and origin = f
}

/* Whether `self` is the 0th parameter of `func`, and `func` is a normal method */
/** INTERNAL -- Do not use */
predicate penultimate_self_param(ControlFlowNode self, FunctionObject func) {
    self.isParameter() and
    exists(Function method |
        method = func.getFunction() and method.isMethod() |
        method.getArg(0).asName().getAFlowNode() = self and
        // `func` is not called as a function in the scope in which it is declared,
        // since the class, of which `func` is to be a method, will not exist
        // at that point.
        not exists(CallNode call |
            call.getScope() = method.getScope() |
            layer0_points_to(call.getFunction(), func, _, _)
        )
    )
}

/** Is there a local store to the same attribute of the same SSA variable as the load? */
predicate penultimate_attribute_store_load_pair(ControlFlowNode stored_value, ControlFlowNode load) {
    exists(SsaVariable var, string name |
        penultimate_attribute_store(var, name, stored_value) and
        penultimate_attribute_load(load, var.getAUse(), name) and
        not exists(CallNode call |
            layer0_call_sets_self_attribute(call, var, name, _) and
            stored_value.strictlyDominates(call) and
            call.strictlyDominates(load)
        )
    )
}

/** This predicate exists primarily to force the correct join ordering. */
private predicate penultimate_attribute_store_load_points_to(ControlFlowNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    exists(ControlFlowNode stored |
        penultimate_attribute_store_load_pair(stored, f) |
        stored.strictlyDominates(f) and
        penultimate_points_to(stored, value, cls, origin)
    )
}

private predicate penultimate_attribute_points_to(ControlFlowNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    not penultimate_prohibited_attribute(f, value, cls) and
    not must_have_boolean_value(f, value.booleanValue().booleanNot()) and
    penultimate_attribute_points_to_candidate(f, value, cls, origin)
}
  
private predicate penultimate_attribute_points_to_candidate(ControlFlowNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    /* Store in same scope as load, and store dominates load */
    penultimate_attribute_store_load_points_to(f, value, cls, origin)
    or
    /* Builtin objects */
    exists(Object obj, string name |
        f.isLoad() and
        penultimate_points_to(f.(AttrNode).getObject(name), obj, _, _) and
        py_cmembers_versioned(obj, name, value, major_version().toString()) and origin = f and
        cls = builtin_object_type(value)
    )
    or
    /* Class attributes */
    penultimate_class_attribute_points_to(f, value, cls, origin)
    or
    /* Module attributes */
    penultimate_module_attribute_points_to(f, value, cls, origin)
    or
    /* Simple instance attributes */
    penultimate_instance_attribute_points_to(f, value, cls, origin)
}

private predicate penultimate_class_attribute_points_to_impl(AttrNode f, Object value, ClassObject cls, ObjectOrCfg origin_or_obj) {
    f.isLoad() and
    exists(ControlFlowNode fval, string name |
        fval = f.getObject(name) |
        /* The 'obvious' formulation of this:
           exists(ClassObject obj |
              penultimate_points_to(fval, obj, _, _) and
              penultimate_class_attribute_lookup(obj, name, value, cls, origin_or_obj)
           )
         * makes for a very large (and thus slow) recursive layer. So we break the recursion.
         * In order to partially make up for the reduction in accuracy, we use both prev/this and this/prev versions.
         */
        exists(ClassObject obj |
            penultimate_points_to(fval, obj, _, _) and
            layer0_class_attribute_lookup(obj, name, value, cls, origin_or_obj)
        )
        or
        exists(ClassObject obj |
            layer0_points_to(fval, obj, _, _) and
            penultimate_class_attribute_lookup(obj, name, value, cls, origin_or_obj)
        )
    )
}

private predicate penultimate_class_attribute_points_to(AttrNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    exists(ObjectOrCfg origin_or_obj |
        penultimate_class_attribute_points_to_impl(f, value, cls, origin_or_obj)
        |
        origin = origin_or_obj
        or
        not origin_or_obj instanceof ControlFlowNode and origin = f
    )
}

private 
ModuleObject penultimate_receiver_module_for(AttrNode f, string name) {
    f.isLoad() and
    exists(ControlFlowNode fval |
        fval = f.getObject(name) |
        penultimate_points_to(fval, result, _, _)
    )
}

pragma [noinline]
private predicate penultimate_receiver_module_for_210(ModuleObject m, string name, AttrNode f) {
    m = penultimate_receiver_module_for(f, name)
}

private 
predicate penultimate_module_attribute_points_to(AttrNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    f.isLoad() and
    exists(ModuleObject obj, string name |
        penultimate_receiver_module_for_210(obj, name, f) |
        exists(ObjectOrCfg origin_or_obj  |
            penultimate_module_attribute_points_to(obj, name, value, cls, origin_or_obj) |
            origin = origin_or_obj.getOrigin()
            or
            not exists(origin_or_obj.getOrigin()) and origin = f
        )
    )
}

/* Helper for instance_attribute_points_to_candidate */
pragma [noinline]
private predicate penultimate_points_to_20(ClassObject cls, Object value) {
    penultimate_points_to(value, _, cls, _)
}

pragma [nomagic]
private predicate attr_stored_outside_init(ClassObject self_class, string attr_name) {
    exists(AttrNode attr, NameNode self, FunctionObject non_init |
        attr.isStore() 
        and 
        self = attr.getObject(attr_name) 
        and 
        self.isSelf() 
        and
        self.getScope() = non_init.getFunction() 
        and
        non_init.getFunction().getScope() = layer0_get_an_improper_super_type(self_class).getPyClass()
        and
        not layer0_method_called_from_init(non_init, self_class) 
    )
}

/** Initialization of attribute in the __init__ method or method called by it,
 * provided that the attribute is not stored to outside ne of those functions.
 */
private AttrNode penultimate_initializer_store(ClassObject self_class, string attr_name) {
    result.isStore() 
    and 
    result.getObject(attr_name).getScope().getScope*() = self_class.getPyClass()
    and
    not attr_stored_outside_init(self_class, attr_name)
    and
    exists(FunctionObject init |
        layer0_method_called_from_init(init, self_class) 
        and
        result.getScope() = init.getFunction()
    )
}

private predicate penultimate_instance_attribute_points_to(ControlFlowNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    /* We are only interested in the simplest attributes here.
     * Defined in initializer exactly and unconditionally once
     */
    /* `f` is `x.attr_name` where `x` is an instance of `self_class` */
    exists(ClassObject self_class, string attr_name |
        exists(ControlFlowNode object |
            not exists(FunctionObject init |
                layer0_method_called_from_init(init, self_class) and
                penultimate_is_self(object) and
                object.getScope() = init.getFunction()  
            ) and
            penultimate_points_to_20(self_class, object) and
            penultimate_attribute_load_120(object, attr_name, f)
        ) and
        exists(ControlFlowNode store |
            store = penultimate_initializer_store(self_class, attr_name) and
            penultimate_points_to(store.(DefinitionNode).getValue(), value, cls, origin)
        )
    ) and not
    layer0_attribute_store_load_pair(_, f)
}

/* INTERNAL -- Use FunctionObject.getAMethodCalledFromInit() instead.
 * Whether the function `method` is called, directly or indirectly, from the `__init__` method of owner */

predicate penultimate_method_called_from_init(FunctionObject method, ClassObject owner) {
    penultimate_class_attribute_lookup(owner, "__init__", method, _, _)
    or
    exists(FunctionObject caller, CallNode call |
        penultimate_method_called_from_init(caller, owner) and
        call.getScope() = caller.getFunction() and
        dominates_all_normal_exits(call) |
        exists(ControlFlowNode self, AttrNode attr, string name, ClassObject mro_type |
            attr = call.getFunction() and
            penultimate_is_self(self) and
            penultimate_super_call(attr.getObject(name), self, mro_type) and
            layer0_class_lookup_in_mro(owner, penultimate_next_in_mro(owner, mro_type), name, method)
        )
        or
        exists(AttrNode self_attr, string name |
            call.getFunction() = self_attr and
            penultimate_is_self(self_attr.getObject(name)) |
            penultimate_class_attribute_lookup(owner, name, method, _, _)
        )
    )
}

private predicate penultimate_is_self(NameNode self) {
    penultimate_self_param(self, _)
    or
    exists(SsaVariable self_var |
        penultimate_self_param(self_var.getDefinition(), _) and
        self = self_var.getAUse()
    )
}

private predicate penultimate_if_exp_points_to(IfExprNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    penultimate_points_to(f.getAnOperand(), value, cls, origin)
}

private predicate penultimate_import_points_to(ControlFlowNode f, ModuleObject value, ControlFlowNode origin) {
    exists(string name, ImportExpr i | 
        i.getAFlowNode() = f and i.getImportedModuleName() = name and
        penultimate_module_imported_as(value, name) and
        origin = f
    )
}

private predicate penultimate_from_import_points_to(ImportMemberNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    /* Three options here:
     * 1. We can infer the module's attribute, and that attribute has an origin
     * 2. We can infer the module's attribute, but the attribute has no origin
     * 3. We can't infer the module's attribute.
     */
    exists(ImportMember im, string name |
        im.getAFlowNode() = f and name = im.getName() |
        exists(ModuleObject mod, ObjectOrCfg origin_or_obj |
            penultimate_points_to(f.getModule(name), mod, _, _) and
            penultimate_module_attribute_points_to(mod, name, value, cls, origin_or_obj) |
            origin = origin_or_obj /* 1. */
            or
            not origin_or_obj instanceof ControlFlowNode and origin = f /* 2. */
        )
        or
        not exists(ModuleObject mod | /* 3. */
            layer0_points_to(f.getModule(name), mod, _, _) and
            layer0_module_attribute_points_to(mod, name, _, _, _)
        ) and f = origin and value = f and cls = penultimate_global_type(value) 
    )
    and
    /* If locally defined in init, then defer to import time points to */
    not is_locally_defined_from_dot_import_in_init(f, _)
    or
    /* Importing from the package in an __init__ module */
    exists(SsaVariable var | 
        locally_defined_from_dot_import_in_init(f, var) and
        penultimate_ssa_variable_points_to(var, value, cls, origin)
    )
    or
    exists(string name |
        is_locally_defined_from_dot_import_in_init(f, name) and
        not locally_defined_from_dot_import_in_init(f, _) and
        exists(PackageObject package |
            package.getInitModule().getModule() = f.getNode().getEnclosingModule() |
            value = package.submodule(name) and origin = f and cls = theModuleType()
        )
    )
}

private predicate nonlocal_variable_points_to(NameNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    f.isNonLocal() and
    (
        /* use points to the same as the SSA variables for var at the end of the function. */
        exists(SsaVariable ssa |
            ssa.getAUse() = f and
            /* There is no other SSA variable that succeeds ssa */
            not exists(SsaVariable succ | succ.getAPhiInput() = ssa) and
            penultimate_ssa_variable_points_to(ssa, value, cls, origin)
        )
        or
        /* Variable is unused except in inner function, so no SSA variable is created */
        not exists(SsaVariable ssa | ssa.getAUse() = f) and
        exists(Variable v | f.uses(v) |
            strictcount(NameNode def | def.defines(v)) = 1 and
            exists(NameNode def | 
                def.defines(v) |
                penultimate_points_to(def, value, cls, origin)
            )
        )
    )
}

/** Whether global variable use `n` refers to `value, cls, origin` and is either a builtin or an import */
private predicate global_builtin_or_import(NameNode n, Object value, ClassObject cls, ControlFlowNode origin) {
   n.isGlobal() 
   and
   not exists(penultimate_get_global_ssa_defn_candidate(_, n))
   and
   not exists(SsaVariable var | var.getAUse() = n | exists(var.getDefinition())) 
   and
   (
       value =  builtin_object(n.getId()) and py_cobjecttypes(value, cls) and origin = n
       or
       /* Defined by import */
       global_import_defn(n, value, cls, origin)
   )
}

private predicate global_import_defn(NameNode n, Object value, ClassObject cls, ControlFlowNode origin) {
   exists(Variable var, ImportStarNode imp, string id |
       var.getALoad() = n.getNode() and
       id = var.getId() and
       penultimate_import_star_defines_object(imp, id, value, cls, origin) and
       import_star_strictly_dominates(imp, n)
   )
}

// evaluable given additional constraints on argument types
private predicate import_star_strictly_dominates(ImportStarNode imp, NameNode n) {
    imp.strictlyDominates(n)
}

private predicate use_points_to_candidate(NameNode n, Object value, ClassObject cls, ControlFlowNode origin) {
   n.isLocal() and 
   exists(SsaVariable var |
       var.getAUse() = n |
       penultimate_ssa_variable_points_to(var, value, cls, origin)
   )
   or
   nonlocal_variable_points_to(n, value, cls, origin)
   or
   penultimate_global_use_points_to(n, value, cls, origin)
   or
   global_builtin_or_import(n, value, cls, origin)
}

/** Get an object pointed to by a use (of a variable) */
private predicate penultimate_use_points_to(NameNode n, Object value, ClassObject cls, ControlFlowNode origin) {
    not penultimate_prohibited_use(n, value, cls) and
    not must_have_boolean_value(n, value.booleanValue().booleanNot()) and
    use_points_to_candidate(n, value, cls, origin)
}

/** Gets an object pointed to by a use with a ssa variable.
 * Note this can be a local variable in a function or class or a global variable at module scope */
pragma [nomagic]
private predicate penultimate_ssa_variable_points_to(SsaVariable var, Object value, ClassObject cls, ControlFlowNode origin) {
    penultimate_points_to(var.getDefinition(), value, cls, origin) and not exists(var.getAPhiInput())
    or
    penultimate_ssa_phi_points_to(var, value, cls, origin)
}

/** What the the SSA variable 'var' may point to, provided that it is a phi node, taking care to account 
 * for guards on the incoming edges. The points-to relation for an SSA phi-node is the union of its incoming 
 * SSA variables, excepting those values and classes that are explicitly guarded against.
 */
private predicate penultimate_ssa_phi_points_to(SsaVariable var, Object value, ClassObject cls, ControlFlowNode origin) {
    exists(SsaVariable incoming, BasicBlock pred, BasicBlock succ |
        pred = var.getPredecessorBlockForPhiArgument(incoming) and succ = var.getDefinition().getBasicBlock() |
        not penultimate_prohibited_on_edge(incoming, pred, succ, value, cls) and
        not must_have_boolean_value_on_edge(incoming, pred, succ, value.booleanValue().booleanNot()) and
        penultimate_ssa_variable_points_to(incoming, value, cls, origin)
    )
}

/** Gets an object pointed to by this definition */
private predicate penultimate_def_points_to(ControlFlowNode n, Object value, ClassObject cls, ControlFlowNode origin) {
    penultimate_points_to(n.(DefinitionNode).getValue(), value, cls, origin)
    or
    /* Default values for parameters */
    n.isParameter() and 
    exists(Parameter p | 
        p.asName().getAFlowNode() = n and 
        penultimate_points_to(p.getDefault().getAFlowNode(), value, cls, origin) 
    )
    or
    /* General parameters, including those with defaults. */
    n.isParameter() and not layer0_self_param(n, _) and value = n and origin = n and cls = theUnknownType()
    or
    exists(FunctionObject meth | penultimate_self_param(n, meth) and penultimate_self_type(meth, cls)) and value = n and origin = n
}

predicate penultimate_abstract_class(ClassObject cls) {
    penultimate_class_explicit_metaclass(cls) = theAbcMetaClassObject()
    or
    exists(string name, FunctionObject unimplemented, Raise r |
        penultimate_class_attribute_lookup(cls, name, unimplemented, _, _) and
        r.getScope() = unimplemented.getFunction() and
        (
            penultimate_points_to(r.getException().getAFlowNode(), theNotImplementedErrorType(), _, _)
            or
            penultimate_points_to(r.getException().getAFlowNode(), _, theNotImplementedErrorType(), _)
        )
    )
}

predicate penultimate_concrete_class(ClassObject cls) {
    penultimate_instantiation(_, cls)
    or
    not layer0_abstract_class(cls)
}

/** Whether `cls` is a possible class of self in `method` */
/* This is public mainly for testing */
predicate penultimate_self_type(FunctionObject method, ClassObject cls) {
    (
        penultimate_concrete_class(cls)
        or
        method.getFunction().getScope() = cls.getPyClass()
    )
    and
    (
        /* Standard call */
        penultimate_class_attribute_lookup(cls, _, method, _, _)
        or
        /* Call via super */
        penultimate_super_method_call(_, cls, method)
    )
}

private predicate penultimate_subscript_load_store_pair(SubscriptNode store, SubscriptNode load) {
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
        penultimate_points_to(store.getIndex(), index, _, _) and
        penultimate_points_to(load.getIndex(), index, _, _)
    )
}

/** Gets an object pointed to by this subscript load */
private predicate penultimate_subscript_points_to(SubscriptNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    exists(SubscriptNode store |
        penultimate_subscript_load_store_pair(store, f) |
        penultimate_points_to(store.(DefinitionNode).getValue(), value, cls, origin)
    )
}

/** Whether `call` is a call to super() with for an object of class `self_type`
 * and the `start` class in the MRO. E.g
 * For a call `super(T, self)`. 
 * `self_type` is `type(self)` and `start` is `T`
 * Handles both Python 2 style `super(T, self)` and Python 3 style `super()`.
 */
 /* This might need to be part of public API */
private predicate penultimate_super_call_types(CallNode call, ClassObject self_type, ClassObject start_type) {
    exists(ClassObject mro_type, ControlFlowNode self |
        start_type = penultimate_next_in_mro(self_type, mro_type) and
        penultimate_super_call(call, self, mro_type) and
        penultimate_points_to_20(self_type, self)
    )
}

/* INTERNAL -- Public for testing only */
predicate penultimate_super_call(CallNode call, ControlFlowNode self, ClassObject mro_type) {
    layer0_points_to(call.getFunction(), theSuperType(), _, _) and
    (
        layer0_points_to(call.getArg(0), mro_type, _, _) and
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

/** Whether `call` is a call to `method` of the form `super(...).method(...)` */
/* Public for testing. */
predicate penultimate_super_method_call(CallNode call, ClassObject self_type, FunctionObject method) {
    exists(AttrNode attr |
        attr = call.getFunction() and
        exists(CallNode super_call, ClassObject start_type, string name |
            // lifted to help join-ordering
            penultimate_super_method_call_helper(attr, self_type, super_call, start_type, name) and
            /* super().name lookup */
            penultimate_class_lookup_in_mro(self_type, start_type, name, method)
        )
    )
}

pragma[noinline]
private predicate penultimate_super_method_call_helper(AttrNode attr, ClassObject self_type, CallNode super_call, ClassObject start_type, string name) {
    penultimate_super_call_types(super_call, self_type, start_type) and 
    layer0_points_to(attr.getObject(name), super_call, _, _)
}

/** INTERNAL -- Do not use */
predicate penultimate_attribute_store(SsaVariable var, string name, ControlFlowNode stored) {
    last_simple_attribute_store_in_scope(var, name, stored)
    or
    extensional_name(name) and
    exists(CallNode call |
        /* This must be part of the previous layer, to prevent incorrect join ordering */
        layer0_points_to(call.getFunction(), builtin_object("setattr"), _, _) and
        var.getAUse() = call.getArg(0) and
        call.getArg(1).getNode().(StrConst).getText() = name and
        call.getArg(2) = stored
    )
}

/* A load of an attribute, either directly or through getattr,
 * `objectuse` is the use of the object with attribute `name`
 */
/** INTERNAL -- Do not use */
predicate penultimate_attribute_load(ControlFlowNode load, ControlFlowNode objectuse, string name) {
  extensional_name(name) and
  (
    exists(AttrNode fload |
        fload = load |
        fload.isLoad() and
        objectuse = fload.getObject(name)
    )
    or
    exists(CallNode call |
        call = load |
        /* This must be part of the previous layer, to prevent incorrect join ordering */
        layer0_points_to(call.getFunction(), builtin_object("getattr"), _, _) and
        objectuse = call.getArg(0) and
        call.getArg(1).getNode().(StrConst).getText() = name
    )
  )
}

pragma [noinline]
private predicate penultimate_attribute_load_120(ControlFlowNode objectuse, string name, ControlFlowNode load) {
     penultimate_attribute_load(load, objectuse, name)
}

private predicate penultimate_self_attribute_store_in_block(BasicBlock b, string attrname, ControlFlowNode stored) {
    extensional_name(attrname) and
    exists(SsaVariable var |
       penultimate_attribute_store(var, attrname, stored) and
       var.isSelf()
    ) and
    stored.getBasicBlock() = b
}

private predicate penultimate_self_attribute_set_in_block(BasicBlock b, string attrname, ControlFlowNode stored) {
    penultimate_self_attribute_store_in_block(b, attrname, stored)
    or
    penultimate_self_attribute_set_in_block(b.getAPredecessor(), attrname, stored)
}

private predicate penultimate_self_attribute_not_set_in_block(BasicBlock b, string attrname) {
    exists(BasicBlock other |
        b.getScope() = other.getScope() |
        penultimate_self_attribute_set_in_block(other, attrname, _)
    )
    and
    not penultimate_self_attribute_store_in_block(b, attrname, _)
    and
    (
        not penultimate_self_attribute_set_in_block(b, attrname, _)
        or
        penultimate_self_attribute_not_set_in_block(b.getAPredecessor(), attrname)
    )
}

/** INTERNAL -- Use `FunctionObject.unconditionallySetsSelfAttribute(attrname)` instead */

predicate penultimate_unconditionally_sets_self_attribute(FunctionObject method, string attrname) {
    extensional_name(attrname) and
    forex(BasicBlock exit |
        exit.getLastNode() = method.getFunction().getANormalExit() |
        penultimate_self_attribute_set_in_block(exit, attrname, _) and
        not penultimate_self_attribute_not_set_in_block(exit, attrname)
    )
}

private predicate penultimate_sets_self_attribute(FunctionObject method, string attrname, ControlFlowNode store) {
    exists(BasicBlock b |
        penultimate_self_attribute_set_in_block(b, attrname, store) |
        b.getLastNode() = method.getFunction().getANormalExit()
    )
}

private predicate penultimate_assigned_in_init(ClassObject cls, string name) {
    exists(FunctionObject init |
        penultimate_class_attribute_lookup(cls, "__init__", init, _, _) and
        penultimate_sets_self_attribute(init, name, _)
    )
}

/** INTERNAL -- Do not use */
predicate penultimate_call_sets_self_attribute(CallNode call, SsaVariable var, string attrname, ControlFlowNode store) {
    extensional_name(attrname) and
    exists(FunctionObject method |
        /* `method` is called by `call` with `var` as the 'self' argument */
        penultimate_self_method_call(method, call, var) and
        penultimate_sets_self_attribute(method, attrname , store)
    )
}

private predicate penultimate_self_method_call(FunctionObject method, CallNode call, SsaVariable self) {
    self.isSelf() and
    call.getFunction().(AttrNode).getObject() = self.getAUse() and
    call = penultimate_get_a_call(method)
}

/** INTERNAL -- Use  ClassObject.getBaseType(n) instead.
 * Gets the nth base class of the class */

Object penultimate_class_base_type(ClassObject cls, int n) {
    exists(ClassExpr cls_expr | cls.getOrigin() = cls_expr |
        penultimate_points_to(cls_expr.getBase(n).getAFlowNode(), result, _, _)
        or
        penultimate_is_new_style(cls) and not exists(cls_expr.getBase(0)) and result = theObjectType() and n = 0
    )
    or
    result = builtin_base_type(cls) and n = 0
}

/** INTERNAL -- Use ClassObject.isNewStyle() instead. */

predicate penultimate_is_new_style(ClassObject cls) {
    cls.isC()
    or
    major_version() >= 3
    or
    exists(cls.declaredMetaClass())
    or
    penultimate_is_new_style(penultimate_class_base_type(cls, _))
}

/** INTERNAL -- Do not use */
predicate penultimate_mro_sparse(ClassObject cls, ClassObject sup, int index) {
    if penultimate_is_new_style(sup) then (
        penultimate_depth_first_indexed(cls, sup, index) and
        not exists(int after | penultimate_depth_first_indexed(cls, sup, after) and after > index)
    ) else (
        penultimate_depth_first_indexed(cls, sup, index) and
        not exists(int before | penultimate_depth_first_indexed(cls, sup, before) and before < index)
    )
}

/** An index for the base class in the mro such that the index for superclasses of the base
 * class are guaranteed not to clash with the superclasses of other base classes.  */
private predicate penultimate_class_base_offset(ClassObject cls, ClassObject base, int index) {
    exists(int n |
        penultimate_class_base_type(cls, n) = base |
        index = sum(ClassObject left_base |
            exists(int i | left_base = penultimate_class_base_type(cls, i) and i < n) |
            count (penultimate_get_an_improper_super_type(left_base))
        )
    )
}

/** Index all super-classes using depth-first search, 
 * numbering parent nodes before their children */
private predicate penultimate_depth_first_indexed(ClassObject cls, ClassObject sup, int index) {
    not penultimate_has_illegal_bases(cls) and penultimate_get_an_improper_super_type(cls) = sup and
    (
        sup = cls and index = 0
        or
        exists(ClassObject base, int base_offset, int sub_index |
            base = penultimate_class_base_type(cls, _) and
            penultimate_class_base_offset(cls, base, base_offset) and
            penultimate_depth_first_indexed(base, sup, sub_index) and
            index = base_offset + sub_index + 1
        )
    )
}

/** INTERNAL -- Use ClassObject.getASuperType() instead */

ClassObject penultimate_get_a_super_type(ClassObject cls) {
    result = penultimate_class_base_type(cls, _)
    or
    result = penultimate_class_base_type(penultimate_get_a_super_type(cls), _)
}

/** INTERNAL -- Use ClassObject.getAnImproperSuperType() instead */

ClassObject penultimate_get_an_improper_super_type(ClassObject cls) {
    result = cls
    or
    result = penultimate_get_a_super_type(cls)
}


/** This class has duplicate base classes */
private predicate penultimate_has_duplicate_bases(ClassObject cls) {
    exists(ClassObject base, int i, int j | i != j and base = penultimate_class_base_type(cls, i) and base = penultimate_class_base_type(cls, j))
}

private predicate penultimate_has_illegal_bases(ClassObject cls) {
    penultimate_has_duplicate_bases(cls) or penultimate_get_an_improper_super_type(penultimate_class_base_type(cls, _)) = cls
}

/** INTERNAL -- Use ClassObject.getMroItem(index) instead */
 cached 

ClassObject penultimate_get_mro_item(ClassObject cls, int index) {
        /* Collapse the sparse array into a dense one */
        exists(int idx | layer0_mro_sparse(cls, result, idx) |
            idx = rank[index](int i, ClassObject s | layer0_mro_sparse(cls, s, i) | i)
        )
}

/** INTERNAL -- ClassObject.nextInMro(sup) instead */

ClassObject penultimate_next_in_mro(ClassObject cls, ClassObject sup) {
    exists(int i |
        sup = penultimate_get_mro_item(cls, i) and
        result = penultimate_get_mro_item(cls, i+1)
    )
}

private int penultimate_declaring_class_index(ClassObject cls, string name) {
    class_declares_attribute(penultimate_get_mro_item(cls, result), name)
}

/** INTERNAL -- ClassObject.lookupMro(start, name) instead */
pragma [nomagic]

predicate penultimate_class_lookup_in_mro(ClassObject cls, ClassObject start, string name, Object object) {
    extensional_name(name) and
    exists(int i, int j |
        start = penultimate_get_mro_item(cls, i) and
        j = penultimate_declaring_class_index(cls, name) and j >= i and 
        not exists(int k | k = penultimate_declaring_class_index(cls, name) and k >= i and k < j) and
        penultimate_class_declared_attribute(penultimate_get_mro_item(cls, j), name, object, _, _)
    )
}

/** INTERNAL -- Use ClassObject.declaredAttribute(name) instead */

predicate penultimate_class_declared_attribute(ClassObject cls, string name, Object value, ClassObject vcls, ObjectOrCfg origin) {
    extensional_name(name) and
    (
      penultimate_object_defined_at_scope_exit(cls.getImportTimeScope(), name, value, vcls, origin)
      or
      value = builtin_class_attribute(cls, name) and class_declares_attribute(cls, name) and 
      origin = value and vcls = builtin_object_type(value)
   )
}

/** INTERNAL -- Use ClassObject.hasAttribute(name) instead */

predicate penultimate_class_has_attribute(ClassObject cls, string name) {
    extensional_name(name) and
    class_declares_attribute(penultimate_get_an_improper_super_type(cls), name)
}

pragma [nomagic]
private ClassObject penultimate_class_supertype_declaring_attr(ClassObject cls, string name) {
    exists(int i |
        i = min(int j | class_declares_attribute(penultimate_get_mro_item(cls, j), name)) |
        result = penultimate_get_mro_item(cls, i)
    )
}

/** INTERNAL -- Use ClassObject.attributeRefersTo(name, vlaue, vlcs, origin) instead
 */
pragma [nomagic]

predicate penultimate_class_attribute_lookup(ClassObject cls, string name, Object value, ClassObject vcls, ObjectOrCfg origin) {
     extensional_name(name) and
   /* Choose attribute declared in (super)class  closest to start of MRO. */
    penultimate_class_declared_attribute(penultimate_class_supertype_declaring_attr(cls, name), name, value, vcls, origin)
}

/** INTERNAL -- Use ClassObject.getMetaClass() instead.
 *  Gets the metaclass for this class */

ClassObject penultimate_class_get_meta_class(ClassObject cls) {
    layer0_has_explicit_metaclass(cls) and result = penultimate_class_explicit_metaclass(cls)
    or
    /* Meta class determination http://gnosis.cx/publish/programming/metaclass_2.html */
    not layer0_has_explicit_metaclass(cls) and result = penultimate_inherited_metaclass(cls)
    or
    /* No declared or inherited metaclass */
    not layer0_has_explicit_metaclass(cls) and not cls.hasABase()
    and 
    ( if baseless_is_new_style(cls) then
          result = theTypeType()
      else
          result = theClassType()
    )
}

/** INTERNAL -- Do not use */
predicate penultimate_has_explicit_metaclass(ClassObject cls) {
    exists(penultimate_class_explicit_metaclass(cls))
}

/** INTERNAL -- Do not use */
ClassObject penultimate_class_explicit_metaclass(ClassObject cls) {
    penultimate_points_to(cls.declaredMetaClass(), result, _, _)
    or
    py_cobjecttypes(cls, result) and is_c_metaclass(result)
    or
    exists(ControlFlowNode meta |
        layer0_six_add_metaclass(_, cls, meta) and
        penultimate_points_to(meta, result, _, _)
    )
}

private ClassObject penultimate_inherited_metaclass(ClassObject cls) {
    result = penultimate_class_explicit_metaclass(penultimate_get_a_super_type(cls))
    and
    forall(ClassObject possibleMeta | 
        possibleMeta = layer0_class_explicit_metaclass(layer0_get_a_super_type(cls)) |
        penultimate_get_an_improper_super_type(result) = possibleMeta
    )
}

/* INTERNAL -- Do not use */
FunctionObject penultimate_six_add_metaclass_function() {
    exists(ModuleObject six |
        six.getName() = "six" and
        penultimate_module_attribute_points_to(six, "add_metaclass", result, _, _)
    )
}

/* INTERNAL -- Do not use */
predicate penultimate_six_add_metaclass(CallNode decorator_call, ClassObject decorated, ControlFlowNode metaclass) {
    exists(CallNode decorator |
        decorator_call.getArg(0) = decorated and
        decorator = decorator_call.getFunction() |
        penultimate_points_to(decorator.getFunction(), penultimate_six_add_metaclass_function(), _, _) and
        decorator.getArg(0) = metaclass
    )
}


/** INTERNAL -- Use ClassObject.failedInference(reason) instead.
 *  Has type inference failed to compute the full class hierarchy for this class for the reason given. */ 

predicate penultimate_failed_inference(ClassObject cls, string reason) {
    strictcount(cls.getPyClass().getADecorator()) > 1 and reason = "Multiple decorators"
    or
    exists(cls.getPyClass().getADecorator()) and not penultimate_six_add_metaclass(_, cls, _) and reason = "Decorator not understood"
    or
    exists(int i | exists(cls.getOrigin().(ClassExpr).getBase(i)) and not exists(layer0_class_base_type(cls, i)) and reason = "Missing base " + i)
    or
    /* Base class is not something we can understand as a class */
    exists(int i |
        exists(cls.getOrigin().(ClassExpr).getBase(i)) |
        exists(Object b | b = penultimate_class_base_type(cls, i) and not b instanceof ClassObject) and reason = "Base " + i + " is not a simple class"
    )
    or
    exists(cls.getPyClass().getMetaClass()) and not layer0_has_explicit_metaclass(cls) and reason = "Failed to infer metaclass"
    or
    exists(int i | penultimate_failed_inference(penultimate_class_base_type(cls, i), _) and reason = "Failed inference for base class at position " + i)
    or
    exists(int i | strictcount(layer0_class_base_type(cls, i)) > 1 and reason = "Multiple bases at position " + i)
}

/** INTERNAL -- Do not use */
pragma [nomagic]
predicate penultimate_module_attribute_points_to(ModuleObject mod, string name, Object value, ClassObject cls, ObjectOrCfg origin) {
    extensional_name(name) and
    (
      penultimate_py_module_attributes(mod.getModule(), name, value, cls, origin)
      or
      penultimate_package_attributes(mod, name, value, cls, origin)
      or
      value = builtin_module_attribute(mod, name) and cls = builtin_object_type(value) and origin = value
    )
}

/** INTERNAL -- Use m.attributeRefersTo(name, obj, origin) instead */

predicate penultimate_py_module_attributes_explicit(Module m, string name, Object obj, ClassObject cls, ControlFlowNode origin) {
    not m.isPackage() and extensional_name(name) and
    (
      exists(SsaVariable var | var.getAUse() = m.getANormalExit() and var.getId() = name |
          penultimate_ssa_variable_points_to(var.getAnUltimateDefinition(), obj, cls, origin)
      )
      or
      penultimate_import_star_defines_object_in_module(m, name, obj, cls, origin)
      or
      exists(DefinitionNode def,  GlobalVariable v |
          v.getScope() = m and v.getId() = name and
          def = penultimate_get_global_ssa_defn_at_scope_end(v, m) and
          penultimate_points_to(def, obj, cls, origin)
      )
    )
}

/** INTERNAL -- Use m.attributeRefersTo(name, obj, origin) instead */

predicate penultimate_py_module_attributes(Module m, string name, Object obj, ClassObject cls, ControlFlowNode origin) {
    not m.isPackage() and extensional_name(name) and
    (
      penultimate_py_module_attributes_explicit(m, name, obj, cls, origin)
      or
      not layer0_py_module_attributes_explicit(m, "__name__", _, _, _) and cls = theStrType() and
      name = "__name__" and obj = object_for_string(m.getName()) and origin = m.getEntryNode()
      or
      /* Set the __package__ to the value specified in the documentation.
       * Note, however, that it is often None in practice as the interpreter sets 
       * the __package__ attribute only when required by the import machinery.
       * We choose the string value in preference to None as it is the steady state value.  
       */
      not layer0_py_module_attributes_explicit(m, "__package__", _, _, _) and name = "__package__" and cls = theStrType() and 
      obj = object_for_string(m.getPackage().getName()) and origin = m.getEntryNode()
    )
}

/** INTERNAL -- Use package.attributeRefersTo(name, obj, origin) instead */

predicate penultimate_package_attributes(PackageObject package, string name, Object obj, ClassObject cls, ControlFlowNode origin) {
    extensional_name(name) and (
      not name = "__name__" and penultimate_module_attribute_points_to(package.getInitModule(), name, obj, cls, origin)
      or
      name = "__name__" and obj = object_for_string(package.getName()) and origin = package.getModule().getEntryNode() and cls = theStrType()
      or
      not layer0_py_module_attributes_explicit(package.getInitModule().getModule(), "__package__", _, _, _) and
      name = "__package__" and obj = object_for_string(package.getName()) and origin = package.getModule().getEntryNode() and cls = theStrType()
      or
      not penultimate_module_defines_name(package.getInitModule().getModule(), name)
      and
      exists(ModuleObject mod |
          mod.getModule() = package.getModule().getSubModule(name) and
          origin = mod.getModule().getEntryNode() and
           obj = mod and
          penultimate_explicitly_imported(mod) and
          cls = theModuleType()
      )
    )
}

/** Whether the module is explicitly imported somewhere */
private predicate penultimate_explicitly_imported(ModuleObject mod) {
    exists(ImportExpr ie | penultimate_module_imported_as(mod, ie.getAnImportedModuleName()))
    or
    exists(ImportMember im | penultimate_module_imported_as(mod, im.getImportedModuleName()))
}

/** Return the Object(s) which can be bound to 'name' upon completion of the code defining this namespace */
private predicate penultimate_object_defined_at_scope_exit(ImportTimeScope scope, string name, Object value, ClassObject cls, ControlFlowNode origin) {
    exists(SsaVariable var | var.getAUse() = scope.getANormalExit() and var.getId() = name |
        penultimate_ssa_variable_points_to(var.getAnUltimateDefinition(), value, cls, origin)
    )
    or
    penultimate_import_star_defines_object_in_module(scope, name, value, cls, origin)
}

/** INTERNAL -- Use ModuleObject.hasAttribute(name)
 *  Whether the module defines name */

predicate penultimate_module_defines_name(Module mod, string name) {
    extensional_name(name) and
    (
        exists(SsaVariable var | name = var.getId() and var.getAUse() = mod.getANormalExit())
        or
        penultimate_import_star_defines_name(mod, name)
    )
}

/* Public API -- Used by UndefinedGlobal query. */

predicate penultimate_import_star_defines_name(Module m, string name) {
    extensional_name(name) and
    exists(ModuleObject imported_module, ImportStar import_stmt |
        penultimate_has_import_star(m, import_stmt, imported_module)
        |
        penultimate_module_exports(imported_module.getModule(), name)
        or
        exists(builtin_module_attribute(imported_module, name))
    )
}

private 
predicate penultimate_import_star_defines_object(ImportStarNode star, string name, Object obj, ClassObject cls, ControlFlowNode origin) {
    extensional_name(name) and
    exists(ModuleObject imported_module |
        /* This is a relatively unimportant way of defining of defining values and breaking the 
         * recursion here gives a big speed up.
         */
        layer0_points_to(star.getModule(), imported_module, _, _) |
        layer0_module_exports(imported_module.getModule(), name) and
        layer0_module_attribute_points_to(imported_module, name, obj, cls, origin)
        or
        origin = star and obj = builtin_module_attribute(imported_module, name) and cls = builtin_object_type(obj)
    )
}

private 
predicate penultimate_import_star_defines_object_in_module(ImportTimeScope scope, string name, Object obj, ClassObject cls, ControlFlowNode origin) {
    extensional_name(name) and
    exists(ImportStarNode import_star |
        import_star.getScope() = scope and
        penultimate_import_star_defines_object(import_star, name, obj, cls, origin)
    )
}

/** INTERNAL -- Use m.exports(name) instead */

predicate penultimate_module_exports(Module m, string name) {
    extensional_name(name) and
    if m.isPackage() then (
        not m.getInitModule().declaredInAll(_) and not name.charAt(0) = "_" and
        exists(ModuleObject sub |
            sub.getModule() = m.getSubModule(name) |
            penultimate_explicitly_imported(sub)
        )
        or
        penultimate_module_exports(m.getInitModule(), name)
    ) else (
        m.declaredInAll(_) and m.declaredInAll(name)
        or
        not m.declaredInAll(_) and penultimate_module_defines_name(m, name) and not name.charAt(0) = "_"
    )
}

/** Does an import star exists in Module m that imports a module called 'name', such that the flow from the import reached the module exit. */
private predicate penultimate_has_import_star(Module m, ImportStar im, ModuleObject imported_module) {
    exists(string name |
        penultimate_module_imported_as(imported_module, name) and
        name = im.getImportedModuleName() and
        im.getScope() = m and
        im.getAFlowNode().getBasicBlock().reachesExit()
    )
}

/** INTERNAL -- Use m.importedAs(name) instead */

predicate penultimate_module_imported_as(ModuleObject m, string name) {
    extensional_name(name) and (
      /* Normal imports */
      m.getName() = name and
      (
          /* Priority:
           * 1. modules not in the stdlib or modules that are the standard lib for this major version
           * 2. modules that are the standard lib for other versions
           *    (in case we run the extractor under a different version)
           */
          not m.getModule().getFile().inStdlib()
          or
          m.getModule().getFile().inStdlib(major_version(), _)
          or
          not exists(Module other |
              other.getName() = name and
              other.getFile().inStdlib(major_version(), _)
          ) and m.getModule().getFile().inStdlib()
      )
      or
      /* sys.modules['name'] = m */
      exists(ControlFlowNode sys_modules_flow, ControlFlowNode n, ControlFlowNode mod |
        /* Use previous points-to here to avoid slowing down the recursion too much */
        exists(SubscriptNode sub, Object sys_modules |
            sub.getValue() = sys_modules_flow and
            layer0_points_to(sys_modules_flow, sys_modules, _, _) and
            sys_modules = builtin_module_attribute(theSysModuleObject(), "modules") and
            sub.getIndex() = n and
            n.getNode().(StrConst).getText() = name and
            sub.(DefinitionNode).getValue() = mod and
            layer0_points_to(mod, m, _, _)
        )
      )
    )
}


/********************
 * VERSION INFO
 */

private predicate penultimate_sys_version_info_index(SubscriptNode s) {
    penultimate_points_to_10(theSysVersionInfoTuple(), s.getValue()) and
    exists(NumericObject zero |
        zero.intValue() = 0 |
        penultimate_points_to(s.getIndex(), zero, _, _)
    )
}

private predicate penultimate_sys_version_info_slice(SubscriptNode s) {
    penultimate_points_to_10(theSysVersionInfoTuple(), s.getValue()) and
    exists(Slice index | index = s.getIndex().getNode() |
        not exists(index.getStart())
    )
}

pragma[noinline]
private predicate penultimate_points_to_10(Object value, ControlFlowNode f) {
    penultimate_points_to(f, value, _, _)
}

private predicate penultimate_comparison(CompareNode cmp, ControlFlowNode fv, ControlFlowNode fc, string opname) {
    exists(Cmpop op |
        cmp.operands(fv, op, fc) and opname = op.getSymbol()
        or
        cmp.operands(fc, op, fv) and opname = reversed(op)
    )
}

/** INTERNAL -- Use Version.getVersion() instead */

predicate penultimate_version_test(CompareNode cmp, Version v) {
    exists(ControlFlowNode fv, ControlFlowNode fc, string opname, int n |
        penultimate_comparison(cmp, fv, fc, opname) and
        version_compare(v, n, opname)
        |
        exists(Object vobj, Object const |
            penultimate_points_to(fv, vobj, _, _) and
            penultimate_points_to(fc, const, _, _)
            |
            penultimate_sys_version_info_index(vobj) and n = const.(NumericObject).intValue()*16
            or
            n = version_tuple_value(const) and
            (penultimate_sys_version_info_slice(vobj) or vobj = theSysVersionInfoTuple())
            or
            vobj = theSysHexVersionNumber() and
            n = scale_hex_version(const.(NumericObject).intValue())
        )
    )
}

private predicate penultimate_os_test(ControlFlowNode f, string os) {
    exists(ControlFlowNode c |
         os_compare(c, os) and
         penultimate_points_to(f, _, _, c)
    )
}

private predicate penultimate_boolean_const(ControlFlowNode f, boolean value) {
    exists(Version v, Object test |
        penultimate_points_to(f, test, _, _) and penultimate_version_test(test, v) |
        value = true and v = major_version()
        or
        value = false and v != major_version()
    )
    or
    exists(string os |
        penultimate_os_test(f, os) |
        value = true and py_flags_versioned("sys.platform", os, major_version().toString())
        or
        value = false and not py_flags_versioned("sys.platform", os, major_version().toString())
    )
    or
    f.getNode() instanceof True and value = true
    or
    f.getNode() instanceof False and value = false
    or
    exists(SsaVariable var |
        var.getAUse() = f and
        penultimate_ssa_boolean_const(var, value)
    )
    or
    exists(ModuleObject mod, string name |
        penultimate_points_to(f.(AttrNode).getObject(name), mod, _, _) and 
        penultimate_attribute_boolean_const(mod, name, value)
    )
}

private predicate penultimate_ssa_boolean_const(SsaVariable var, boolean value) {
    penultimate_boolean_const(var.getDefinition().(DefinitionNode).getValue(), value)
    or
    forex(SsaVariable input |
        input = var.getAPhiInput() |
        penultimate_ssa_boolean_const(input, value)
    )
    or
    exists(ConditionBlock guard, boolean sense |
        penultimate_boolean_const(guard.getLastNode(), sense) |
        exists(SsaVariable in1 |
            in1 = var.getAPhiInput() |
            guard.controls(in1.getDefinition().getBasicBlock(), sense) and penultimate_ssa_boolean_const(in1, value)
            or
            /* Oh why do I still need to do this? */
            (value = true or value = false) and
            guard.controls(in1.getDefinition().getBasicBlock(), sense.booleanNot()) and penultimate_ssa_boolean_const(in1, value.booleanNot())
        )
    )
}

private predicate penultimate_attribute_boolean_const(ModuleObject mod, string name, boolean value) {
    exists(SsaVariable var | var.getAUse() = mod.getModule().getANormalExit() and var.getId() = name |
        penultimate_ssa_boolean_const(var, value)
    )
}


/** INTERNAL -- Whether this ControlFlowNode is pruned due to version or OS constraints. */
predicate penultimate_pruned(ControlFlowNode f) {
    exists(ConditionBlock guard |
        guard.controls(f.getBasicBlock(), true) and penultimate_boolean_const(guard.getLastNode(), false)
        or
        guard.controls(f.getBasicBlock(), false) and penultimate_boolean_const(guard.getLastNode(), true)
    )
}


/* Function related points-to. This needs to be here rather than in FunctionObject, as
 * it may be required by points-to extensions.
 */

/** INTERNAL -- Use FunctionObject.neverReturns() instead.
 *  Whether function `func` never returns. Slightly conservative approximation, this predicate may be false
 * for a function that can never return. */
 
predicate penultimate_function_never_returns(FunctionObject func) {
    /* A Python function never returns if it has no normal exits that are not dominated by a
     * call to a function which itself never returns.
     */
        exists(Function f | f = func.getFunction() |
        not exists(ControlFlowNode exit |
            exit = f.getANormalExit()
            and
            not exists(FunctionObject callee, BasicBlock call  |
                penultimate_get_a_call(callee).getBasicBlock() = call and
                penultimate_function_never_returns(callee) and
                call.dominates(exit.getBasicBlock())
            )
        )
    )
    or
    func = theExitFunctionObject()
    or
    /* Special case "obvious" non-returning functions when points-to has otherwise failed */
    exists(Function f | f = func.getFunction() |
        not f.getAStmt() instanceof If and
        exists(ExprStmt last |
            last = f.getStmt(count(f.getAStmt())-1) |
            last.getValue().(Call).getFunc().(Attribute).getObject("exit").(Name).getId() = "sys"
        )
    )
}

/** INTERNAL -- Use FunctionObject.getACall() */

CallNode penultimate_get_a_call(FunctionObject func) {
    penultimate_function_call(func, result)
    or
    penultimate_method_call(func, result)
}

/** INTERNAL -- Use FunctionObject.getAFunctionCall() */

predicate penultimate_function_call(FunctionObject func, CallNode call) {
    penultimate_points_to(call.getFunction(), func, _, _)
}

/** INTERNAL -- Use FunctionObject.getAMethodCall() */
pragma [nomagic]

predicate penultimate_method_call(FunctionObject func, CallNode call) {
    exists(ControlFlowNode attr, ClassObject cls, string name |
        attr = call.getFunction() and
        penultimate_receiver_type_for(cls, name, attr) and
        penultimate_class_attribute_lookup(cls, name, func, _, _)
    )
    or
    penultimate_super_method_call(call, _, func)
}

/** INTERNAL -- Do not use. This is part of the internal API.
 * Whether cls `cls` is the receiver type of an attribute access `n`.
 *  Also bind the name of the attribute.
 */

predicate penultimate_receiver_type_for(ClassObject cls, string name, ControlFlowNode n) {
  extensional_name(name) and
  (
    /* `super().meth()` is not a method on `super` */
    cls != theSuperType() and
    exists(Object o |
        /* list.__init__() is not a call to type.__init__() */
        not o instanceof ClassObject |
        penultimate_points_to(n.(AttrNode).getObject(name), o, cls, _)
    )
    or
    exists(PlaceHolder p, Variable v | 
        n.getNode() = p and n.(NameNode).uses(v) and name = v.getId() and
        p.getScope().getScope() = cls.getPyClass()
    )
  )
}

pragma [nomagic]
private ControlFlowNode penultimate_get_argument_for_call_by_position(FunctionObject func, CallNode call, int position) {
    penultimate_method_call(func, call) and
    (
        result = call.getArg(position-1)
        or
        position = 0 and result = call.getFunction().(AttrNode).getObject()
    )
    or
    penultimate_function_call(func, call) and
    result = call.getArg(position)
}

private predicate keyword_value_for_call(CallNode call, string name, ControlFlowNode value) {
    exists(Keyword kw |
        call.getNode().getAKeyword() = kw |
        kw.getArg() = name and kw.getValue() = value.getNode() and
        value.getBasicBlock().dominates(call.getBasicBlock())
    )
}

private ControlFlowNode penultimate_get_argument_for_call_by_name(FunctionObject func, CallNode call, string name) {
    call = penultimate_get_a_call(func) and 
    keyword_value_for_call(call, name, result)
}

/** INTERNAL -- Use FunctionObject.getArgumentForCall(call, position) instead.  */

ControlFlowNode penultimate_get_positional_argument_for_call(FunctionObject func, CallNode call, int position) {
    result = penultimate_get_argument_for_call_by_position(func, call, position)
    or
    exists(string name |
        result = penultimate_get_argument_for_call_by_name(func, call, name) and
        func.getFunction().getArg(position).asName().getId() = name
    )
}

/** INTERNAL -- Use FunctionObject.getNamedArgumentForCall(call, name) instead.  */

ControlFlowNode penultimate_get_named_argument_for_call(FunctionObject func, CallNode call, string name) {
  extensional_name(name) and
  (
    result = penultimate_get_argument_for_call_by_name(func, call, name)
    or
    exists(int position |
        result = penultimate_get_argument_for_call_by_position(func, call, position) and
        func.getFunction().getArg(position).asName().getId() = name
    )
  )
}

/**
 * Whether this implictly returns an object
 */
private predicate penultimate_implicitly_returns(PyFunctionObject func, Object none_, ClassObject noneType) {
   noneType = theNoneType() and not func.getFunction().isGenerator() and none_ = theNoneObject() and
   (
     not exists(func.getAReturnedNode()) and exists(func.getFunction().getANormalExit())
     or
     exists(Return ret | ret.getScope() = func.getFunction() and not exists(ret.getValue()))
   )
}

/** INTERNAL -- Use FunctionObject.getAnInferredReturnType() instead.  */

ClassObject penultimate_get_an_inferred_return_type(FunctionObject func) {
     func.getFunction().isGenerator() and result = theGeneratorType()
     or
     not layer0_function_never_returns(func) and not func.getFunction().isGenerator() and
     (
       penultimate_points_to(func.(PyFunctionObject).getAReturnedNode(), _, result, _)
       or
       penultimate_implicitly_returns(func, _, result)
       or 
       /* If the origin of the the return node is a call to another function, then this function will return the type of that call 
        * Note: since runtime_points_to() is intra-procedural, we need to handle the return types of calls explicitly here. */
       exists(FunctionObject callee |
           penultimate_points_to(func.(PyFunctionObject).getAReturnedNode(), _, theUnknownType(), callee.getACall()) |
           result = penultimate_get_an_inferred_return_type(callee)
       )
     )
     or
     result = func.(BuiltinCallable).getAReturnType()
}

FunctionObject penultimate_get_a_callee(Scope s) {
    exists(ControlFlowNode node |
        node.getScope() = s and
        node = penultimate_get_a_call(result)
    )
}

// Helper for scope_precedes
private predicate penultimate_scope_executes(Scope caller, Scope callee, ControlFlowNode exec) {
    exists(FunctionObject f |
        caller = exec.getScope() and f.getFunction() = callee and exec = layer0_get_a_call(f)
    )
    or
    caller = exec.getScope() and
    exec.getNode().(ClassExpr).getInnerScope() = callee
}

// Helper for scope_precedes
private predicate penultimate_scope_calls(Scope caller, Scope callee) {
    penultimate_scope_executes(caller, callee, _)
    or
    exists(Scope mid |
        penultimate_scope_calls(mid, callee) and
        penultimate_scope_calls(caller, mid)
    )
}

// Temporal scope ordering.
predicate penultimate_scope_precedes(Scope pre, Scope post, int ranking) {
    not penultimate_scope_calls(pre, post) and
    not penultimate_scope_calls(post, pre) and
    base_scope_precedes(pre, post, ranking)
}

/** Do not use -- For testing purposes */
predicate penultimate_global_phi_definition(GlobalVariable v, BasicBlock phi) {
    exists(BasicBlock x, ControlFlowNode defnode | 
        defnode = x.getNode(_) and
        x.dominanceFrontier(phi) and penultimate_global_ssa_defn(v, defnode, _)
    )
}

/** Whether scope `s` uses`v` either directly in one of its callees. */
private predicate penultimate_scope_uses_global(GlobalVariable v, Scope s) {
    v.getALoad().getScope() = s
    or
    exists(Function callee |
        layer0_get_a_callee(s).getFunction() = callee and
        penultimate_scope_uses_global(v, callee)
   )
}

/** Whether scope `s` defines `v` either directly in one of its callees. */
private predicate penultimate_scope_defines_global(GlobalVariable v, Scope s) {
    v.getAStore().getScope() = s
    or
    exists(Function callee |
        layer0_get_a_callee(s).getFunction() = callee and
        penultimate_scope_defines_global(v, callee)
   )
}

/** Do not use -- For testing only.
 * Whether scope `pre` pre-defines `v` for the global-SSA variable `(v, entry)` where `entry` is the entry point to a scope.
 */
predicate penultimate_global_prev_scope(GlobalVariable v, ControlFlowNode entry, Scope pre) {
    exists(Scope post |
        post.getEntryNode() = entry and
        penultimate_scope_uses_global(v, post) and
        exists(penultimate_get_global_ssa_defn_at_scope_end(v, pre)) |
        penultimate_scope_precedes(pre, post, 1) or
        penultimate_scope_precedes(pre, post, 2) and
        not exists(Scope better, ControlFlowNode defn |
            defn.getScope() = better and
            penultimate_scope_precedes(better, post, 1) and
            layer0_global_ssa_defn(v, defn, _)
        )
    )
}

pragma [noopt]
private predicate penultimate_global_defn_from_callsite(GlobalVariable v, ControlFlowNode entry, ControlFlowNode callsite, ControlFlowNode defn) {
    exists(Scope callee |
        non_module_scope_defines_or_uses_global(callee, v) and
        penultimate_scope_executes(_, callee, callsite) and
        entry = callee.getEntryNode()
    ) and
    penultimate_global_ssa_defn(v, defn, _) and
    // manually inlined ControlFlowNode.strictlyDominates so that we can use pragma[noopt]
    (
        exists(BasicBlock bb1, BasicBlock bb2 |
            defn.getBasicBlock() = bb1
            and
            callsite.getBasicBlock() = bb2
            and
            bb1.strictlyDominates(bb2)
        )
        or
        exists(BasicBlock b, int i, int j |
            defn = b.getNode(i)
            and
            callsite = b.getNode(j)
            and
            i < j
        )
    )
}

private predicate penultimate_global_builtin_definition(GlobalVariable v, ControlFlowNode entry, Object value, ClassObject cls) {
    exists(Module m |
        v.getScope() = m and m.getEntryNode() = entry and
        value = builtin_object(v.getId()) and
        py_cobjecttypes(value, cls)
    )
}

private predicate penultimate_global_defn_in_class(GlobalVariable v, ControlFlowNode defn, Class scope) {
    exists(ClassExpr cls |
        cls.getAFlowNode() = defn  and
        scope = cls.getInnerScope() |
        penultimate_scope_defines_global(v, scope)
    )
}

/** DO NOT USE -- Internal, for testing. 
 * Whether `node` is the location of a global-SSA definition of `v`. `kind` describes the sort of definition for testing purposes.
 */
predicate penultimate_global_ssa_defn(GlobalVariable v, ControlFlowNode node, string kind) {
    penultimate_global_builtin_definition(v, node, _, _) and kind = "builtin"
    or
    penultimate_global_phi_definition(v, node) and kind = "phi"
    or
    node.(NameNode).defines(v) and kind = "assignment"
    or
    node.(NameNode).deletes(v) and kind = "deletion"
    or
    penultimate_global_callsite_defines_variable(v, node, _) and kind = "callsite"
    or
    penultimate_global_prev_scope(v, node, _) and kind = "previous scope"
    or
    penultimate_global_defn_from_callsite(v, node, _, _) and kind = "caller scope"
    or
    penultimate_global_defn_in_class(v, node, _) and kind = "in class"
}

/** 
 * Whether the function `callee`, called from `callsite`, defines the global variable `v`
 */
private predicate penultimate_global_callsite_defines_variable(GlobalVariable v, CallNode callsite, Function callee) {
    penultimate_scope_defines_global(v, callee) and
    v.getScope() = callsite.getEnclosingModule() and
    exists(PyFunctionObject fo |
        callee = fo.getFunction() and
        callsite = layer0_get_a_call(fo)
    )
}

pragma[noopt]
private ControlFlowNode penultimate_get_global_ssa_defn_candidate(GlobalVariable v, NameNode use) {
    use.uses(v) and penultimate_global_ssa_defn(v, result, _) and
    // manually inlined ControlFlowNode.dominates so that we can use pragma[noopt]
    (
        exists(BasicBlock bb1, BasicBlock bb2 | 
            result.getBasicBlock() = bb1 
            and
            use.getBasicBlock() = bb2 
            and
            bb1.strictlyDominates(bb2)
        )
        or
        exists(BasicBlock b, int i, int j |
            result = b.getNode(i) 
            and
            use = b.getNode(j) 
            and
            i <= j
        )
    )
}

/** Do not use -- For testing only */ 
ControlFlowNode penultimate_get_global_ssa_defn(GlobalVariable v, NameNode use) {
    use.uses(v) and
    result = penultimate_get_global_ssa_defn_candidate(v, use) and
    not exists(ControlFlowNode better |
        better = penultimate_get_global_ssa_defn_candidate(v, use) and
        result.strictlyDominates(better)
    )
}

pragma[noinline]
private predicate scope_exit(ControlFlowNode node, ControlFlowNode exit, Scope f) {
    node.getScope() = f and
    exit = f.getANormalExit() and
    /* Must be dominates, not strictly-dominates as exit can be a phi-node */
    node.dominates(exit)
}

/** INTERNAL -- Do not use */
ControlFlowNode penultimate_get_global_ssa_defn_at_scope_end_candidate(GlobalVariable v, Scope f) {
    penultimate_global_ssa_defn(v, result, _) and
    scope_exit(result, _, f)
}

/** Do not use -- testing only.
 * Get the best (closest) definition of `v` reaching the end of scope `f`
 */
pragma[nomagic]
ControlFlowNode penultimate_get_global_ssa_defn_at_scope_end(GlobalVariable v, Scope f) {
    result = penultimate_get_global_ssa_defn_at_scope_end_candidate(v, f) and
    not exists(ControlFlowNode better |
        better = layer0_get_global_ssa_defn_at_scope_end_candidate(v, f) and
        result.strictlyDominates(better)
    )
}

/** Get the best (closest dominating) definition of `v` for callsite `call` (and callee entry point `entry`) */
private 
ControlFlowNode penultimate_get_best_defn_for_callsite(GlobalVariable v, ControlFlowNode call, ControlFlowNode entry) {
    penultimate_global_defn_from_callsite(v, entry, call, result) and
    not exists(ControlFlowNode better |
        penultimate_global_defn_from_callsite(v, entry, call, better) and
        result.strictlyDominates(better)
    )
}

/** Whether the global SSA variable `(v, defn)` points-to `(value, cls, origin)` where `defn` is the entry point of a function. */ 
private 
predicate penultimate_global_callee_ssa_points_to(GlobalVariable v, ControlFlowNode defn, Object value, ClassObject cls, ControlFlowNode origin) {
    exists(ControlFlowNode call, ControlFlowNode outer_defn |
        outer_defn = penultimate_get_best_defn_for_callsite(v, call, defn) and
        penultimate_global_ssa_points_to(v, outer_defn, value, cls, origin, _)
    )
}

/** Do not use -- testing only.
 * Whether the global SSA variable `(v, defn)` points-to `(value, cls, origin)`. The `kind` string is for testing.
 */
pragma [nomagic]
predicate penultimate_global_ssa_points_to(GlobalVariable v, ControlFlowNode defn, Object value, ClassObject cls, ControlFlowNode origin, string kind) {
    penultimate_global_builtin_definition(v, defn, value, cls) and origin = defn and kind = "builtin"
    or
    exists(Function f, ControlFlowNode d |
        penultimate_global_callsite_defines_variable(v, defn, f) and
        d = penultimate_get_global_ssa_defn_at_scope_end(v, f) and
        penultimate_global_ssa_points_to(v, d, value, cls, origin, _)
    ) and kind = "callsite"
    or
    defn.(NameNode).defines(v) and penultimate_points_to(defn, value, cls, origin) and kind = "assignment"
    or
    penultimate_global_ssa_phi_points_to(v, defn, value, cls, origin) and kind = "phi"
    or
    exists(Scope pre, ControlFlowNode def |
        penultimate_global_prev_scope(v, defn, pre) and
        def = penultimate_get_global_ssa_defn_at_scope_end(v, pre) and
        penultimate_global_ssa_points_to(v, def, value, cls, origin, _)
    ) and kind = "previous scope"
    or
    penultimate_global_callee_ssa_points_to(v, defn, value, cls, origin) and kind = "caller scope"
    or
    exists(Class inner, ControlFlowNode d |
        penultimate_global_defn_in_class(v, defn, inner) and
        d = penultimate_get_global_ssa_defn_at_scope_end(v, inner) and
        penultimate_global_ssa_points_to(v, d, value, cls, origin, _)
    ) and kind = "in class"
}

/** What the the SSA variable 'var' may point to, provided that it is a phi node, taking care to account 
 * for guards on the incoming edges. The points-to relation for an SSA phi-node is the union of its incoming 
 * SSA variables, excepting those values and classes that are explicitly guarded against.
 */
predicate penultimate_global_ssa_phi_points_to(GlobalVariable v, BasicBlock phi, Object value, ClassObject cls, ControlFlowNode origin) {
    penultimate_global_phi_definition(v, phi) and
    exists(ControlFlowNode incoming_defn, BasicBlock pred |
        incoming_defn = penultimate_get_phi_argument_for_predecessor_block(v, phi, pred) |
        not penultimate_global_prohibited_on_edge(v, incoming_defn, pred, phi, value, cls) and
        not penultimate_global_must_have_boolean_value_on_edge(v, incoming_defn, pred, phi, value.booleanValue().booleanNot()) and
        penultimate_global_ssa_points_to(v, incoming_defn, value, cls, origin, _)
    )
}
/** INTERNAL -- Do not not use */
pragma [inline]
predicate penultimate_global_prohibited_on_edge(ControlledVariable var, ControlFlowNode defn, BasicBlock pred, BasicBlock succ, Object value, ClassObject cls) {
    exists(Layer0PointsToFilter cond |
        defn = penultimate_get_global_ssa_defn(var, cond.getRelevantUse(var))
    |
        cond.controlsEdge(var, pred, succ, true)
        and not cond.allowedValue(var, value)
        and not cond.allowedClass(cls) 
        or
        cond.controlsEdge(var, pred, succ, false) and cond.allowedValue(var, value)
        or
        cond.controlsEdge(var, pred, succ, false) and cond.allowedClass(cls)
    )
}

/** Whether f is a use of a variable and the value of that use must be tf */
predicate penultimate_global_must_have_boolean_value_on_edge(GlobalVariable var, ControlFlowNode defn, BasicBlock pred, BasicBlock succ, boolean tf) {
    exists(IsTrue ist |
        ist.controlsEdge(var.(ControlledVariable), pred, succ, tf) and
        defn = penultimate_get_global_ssa_defn(var, ist)
    )
}

pragma[nomagic]
private predicate defn_for_phi(ControlFlowNode defn, ControlFlowNode phi, GlobalVariable v) {
    penultimate_global_phi_definition(v, phi) and
    penultimate_global_ssa_defn(v, defn, _)
}

pragma [noopt]
private ControlFlowNode penultimate_dominating_defn_for_phi_predecessor_block(GlobalVariable v, BasicBlock phi, BasicBlock pred) {
    defn_for_phi(result, phi, v) and
    exists(BasicBlock bb | 
        result.getBasicBlock() = bb 
        and 
        bb.dominates(pred)
    ) and
    pred = phi.getAPredecessor()
}

/** DO NOT USE -- For testing only */
ControlFlowNode penultimate_get_phi_argument_for_predecessor_block(GlobalVariable v, BasicBlock phi, BasicBlock pred) {
    result = penultimate_dominating_defn_for_phi_predecessor_block(v, phi, pred) and
    not exists(ControlFlowNode better |
        better = penultimate_dominating_defn_for_phi_predecessor_block(v, phi, pred) and
        result.strictlyDominates(better)
    )
}

/** Get an object pointed to by a use (of a global variable) */
predicate penultimate_global_use_points_to(NameNode use, Object value, ClassObject cls, ControlFlowNode origin) {
    exists(GlobalVariable v, ControlFlowNode defn, ControlFlowNode ssa_origin |
        defn = penultimate_get_global_ssa_defn(v, use) and
        penultimate_global_ssa_points_to(v, defn, value, cls, ssa_origin, _) 
        |
        if exists(Module m | ssa_origin = m.getEntryNode()) then
            origin = use
        else
            origin = ssa_origin
    )
    or
    use.isGlobal() and not exists(penultimate_get_global_ssa_defn(_, use)) and
    value = builtin_object(use.getId()) and py_cobjecttypes(value, cls) and
    origin = use
}
