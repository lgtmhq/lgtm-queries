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
 * The main relation final_points_to(node, object, cls, origin) relates a control flow node
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
private import Penultimate

private ClassObject final_global_type(Object value) {
    result = final_known_global_type(value)
    or
    not exists(penultimate_known_global_type(value)) and result = theUnknownType()
}


/* Helper for global_type */
/** INTERNAL -- Do not use */
ClassObject final_known_global_type(Object value) {
    result = simple_types(value)
    or
    result = final_class_get_meta_class(value)
    or
    final_instantiation(value, result)
}

/** INTERNAL -- Do not not use */
pragma[inline]
predicate final_prohibited_attribute(AttrNode f, Object value, ClassObject cls) {
    exists(PenultimatePointsToFilter cond, SsaVariable var, string name |
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
predicate final_prohibited_use(NameNode f, Object value, ClassObject cls) {
    exists(PenultimatePointsToFilter cond, ControlledVariable var |
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
predicate final_prohibited_on_edge(ControlledVariable var, BasicBlock pred, BasicBlock succ, Object value, ClassObject cls) {
    exists(PenultimatePointsToFilter cond |
        cond.controlsEdge(var, pred, succ, true)
        and not cond.allowedValue(var, value)
        and not cond.allowedClass(cls) 
        or
        cond.controlsEdge(var, pred, succ, false) and cond.allowedValue(var, value)
        or
        cond.controlsEdge(var, pred, succ, false) and cond.allowedClass(cls)
    )
}

private predicate final_points_to_candidate(ControlFlowNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    kwargs_points_to(f, cls) and value = f and origin = f
    or
    varargs_points_to(f, cls) and value = f and origin = f
    or
    base_points_to(f, value, origin) and cls = final_global_type(value)
    or
    final_attribute_points_to(f, value, cls, origin)
    or
    final_if_exp_points_to(f, value, cls, origin)
    or
    final_import_points_to(f, value, origin) and cls = theModuleType()
    or
    final_from_import_points_to(f, value, cls, origin)
    or
    final_use_points_to(f, value, cls, origin)
    or
    final_def_points_to(f, value, cls, origin)
    or
    final_subscript_points_to(f, value, cls, origin) 
    or
    final_call_points_to(f, value, cls, origin)
    or
    final_sys_version_info_slice(f) and value = f and origin = f and cls = theTupleType()
    or
    final_sys_version_info_index(f) and value = f and origin = f and cls = theIntType()
    or
    final_six_metaclass_points_to(f, value, cls, origin)
    or
        f.(FinalCustomPointsToFact).pointsTo(value, cls, origin)
}

private predicate final_six_metaclass_points_to(ControlFlowNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    exists(ControlFlowNode meta |
        penultimate_six_add_metaclass(f, value, meta) and
        final_points_to(meta, cls, _, _)
    ) and
    origin = value
}


/** INTERNAL -- Use f.refersTo(value, cls, origin) instead */
cached
predicate final_points_to(ControlFlowNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    not penultimate_pruned(f) and
    final_points_to_candidate(f, value, cls, origin)
}

/* A call to type() with a single argument */
/** INTERNAL -- Do not use */
cached
predicate final_call_to_type(CallNode f) {
    final_points_to(f.getFunction(), theTypeType(), _, _) and not exists(f.getArg(1))
}

/* Whether a call to this class may not return an instance of this class. */
/** INTERNAL -- Do not not use */
predicate final_callToClassMayNotReturnInstance(ClassObject cls) {
    /* Django does this, so we need to account for it */
    final_assigned_in_init(cls, "__class__")
    or
    exists(ClassObject s | s = final_get_an_improper_super_type(cls) |
        /* Most builtin types "declare" __new__, such as `int`, yet are well behaved. */
        not s.isC() and class_declares_attribute(s, "__new__")
    )
}

/** Instantiation of an object */
private predicate final_instantiation(CallNode f, ClassObject cls) {
    final_points_to(f.getFunction(), cls, _, _) and
    not penultimate_call_to_type(f) and
    not penultimate_callToClassMayNotReturnInstance(cls)
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
    final_call_to_type(f) and
    cls = theTypeType() and
    (
        final_points_to(f.getArg(0), _, value, _) and
        not value = theUnknownType() and
        (origin.getNode() = value.getOrigin() or /* 1 */
         not exists(value.getOrigin()) and origin = f /* 2 */
        )
        or
        not exists(ClassObject argcls | /* 3 */
            penultimate_points_to(f.getArg(0), _, argcls, _) and
            not argcls = theUnknownType()
        ) and
        value = f and
        origin = f
    )
}

/** INTERNAL -- Do not use */
predicate final_call_not_understood(CallNode f) {
    final_instantiation_irregular_class(f)
    or
    not final_call_to_type(f) and
    not final_instantiation(f, _) and
    not exists(BuiltinFunctionObject b | 
        final_points_to(f.getFunction(), b, _, _) and
        exists(b.getAReturnType())
    ) and
    not final_six_add_metaclass(f, _, _) and
    /* Avoid having two differing values for `getattr(obj, 'name')` */
    not final_attribute_load(f, _, _) and
    not exists(PyFunctionObject func |
        f = final_get_a_call(func)
    )
}

/** INTERNAL -- Do not use */
predicate final_instantiation_regular_class(CallNode f) {
    exists(ClassObject maybe_cls |
        final_points_to(f.getFunction(), maybe_cls, _, _) and
        not final_callToClassMayNotReturnInstance(maybe_cls)
    )
}

private predicate final_instantiation_irregular_class(CallNode f) {
    exists(ClassObject maybe_cls |
        final_points_to(f.getFunction(), maybe_cls, _, _) and
        final_callToClassMayNotReturnInstance(maybe_cls)
    )
}

private predicate final_call_points_to_4(CallNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    not penultimate_call_to_type(f) and
    penultimate_instantiation_regular_class(f) and value = f and final_points_to(f.getFunction(), cls, _, _) and origin = f
}

private predicate final_call_points_to_6(CallNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    exists(BuiltinFunctionObject b |    
        final_points_to(f.getFunction(), b, _, _) and
        cls = b.getAReturnType()
    ) and
    f = origin and value = f
}

private predicate final_call_to_procedure_points_to(CallNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    exists(PyFunctionObject func |
        f = final_get_a_call(func) and
        final_implicitly_returns(func, value, cls) and origin.getNode() = func.getOrigin()
    )
}

private predicate final_call_to_generator_points_to(CallNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    exists(PyFunctionObject func |
        f = final_get_a_call(func) |
        func.getFunction().isGenerator() and origin = f and value = f and cls = theGeneratorType()
    )
}

private predicate final_call_to_function_which_returns_argument_points_to(CallNode call, Object value, ClassObject cls, ControlFlowNode origin) {
   exists(PyFunctionObject func, int n |
        func.unconditionallyReturnsParameter(n) and
        final_points_to(final_get_positional_argument_for_call(func, call, n), value, cls, origin)
    )
}

private predicate final_call_points_to_7(CallNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    exists(ControlFlowNode rval |
        exists(PyFunctionObject func |
            f = final_get_a_call(func) and
            not func = penultimate_six_add_metaclass_function() |
            rval = safe_return_node(func)
        ) and
        final_points_to(rval, value, cls, origin)
    )
    and not is_parameter_default(origin)
}

/** A call, including calls to type(arg), functions and classes */
private predicate final_call_points_to(CallNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    call_to_type_points_to(f, value, cls, origin)
    or
    final_call_points_to_4(f, value, cls, origin)
    or
    final_call_points_to_6(f, value, cls, origin)
    or
    /* Case 7a */
    final_call_points_to_7(f, value, cls, origin)
    or
    /* Case 7b */
    final_call_to_generator_points_to(f, value, cls, origin)
    or
    /* Case 7c */
    final_call_to_function_which_returns_argument_points_to(f, value, cls, origin)
    or
    /* Case 7d */
    final_call_to_procedure_points_to(f, value, cls, origin)
    or
    /* Cases 5 and 8 */
    penultimate_call_not_understood(f) and value = f and cls = theUnknownType() and origin = f
}

/* Whether `self` is the 0th parameter of `func`, and `func` is a normal method */
/** INTERNAL -- Do not use */
predicate final_self_param(ControlFlowNode self, FunctionObject func) {
    self.isParameter() and
    exists(Function method |
        method = func.getFunction() and method.isMethod() |
        method.getArg(0).asName().getAFlowNode() = self and
        // `func` is not called as a function in the scope in which it is declared,
        // since the class, of which `func` is to be a method, will not exist
        // at that point.
        not exists(CallNode call |
            call.getScope() = method.getScope() |
            penultimate_points_to(call.getFunction(), func, _, _)
        )
    )
}

/** Is there a local store to the same attribute of the same SSA variable as the load? */
predicate final_attribute_store_load_pair(ControlFlowNode stored_value, ControlFlowNode load) {
    exists(SsaVariable var, string name |
        final_attribute_store(var, name, stored_value) and
        final_attribute_load(load, var.getAUse(), name) and
        not exists(CallNode call |
            penultimate_call_sets_self_attribute(call, var, name, _) and
            stored_value.strictlyDominates(call) and
            call.strictlyDominates(load)
        )
    )
}

/** This predicate exists primarily to force the correct join ordering. */
private predicate final_attribute_store_load_points_to(ControlFlowNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    exists(ControlFlowNode stored |
        final_attribute_store_load_pair(stored, f) |
        stored.strictlyDominates(f) and
        final_points_to(stored, value, cls, origin)
    )
}

private predicate final_attribute_points_to(ControlFlowNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    not final_prohibited_attribute(f, value, cls) and
    not must_have_boolean_value(f, value.booleanValue().booleanNot()) and
    final_attribute_points_to_candidate(f, value, cls, origin)
}
  
private predicate final_attribute_points_to_candidate(ControlFlowNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    /* Store in same scope as load, and store dominates load */
    final_attribute_store_load_points_to(f, value, cls, origin)
    or
    /* Builtin objects */
    exists(Object obj, string name |
        f.isLoad() and
        final_points_to(f.(AttrNode).getObject(name), obj, _, _) and
        py_cmembers_versioned(obj, name, value, major_version().toString()) and origin = f and
        cls = builtin_object_type(value)
    )
    or
    /* Class attributes */
    final_class_attribute_points_to(f, value, cls, origin)
    or
    /* Module attributes */
    final_module_attribute_points_to(f, value, cls, origin)
    or
    /* Simple instance attributes */
    final_instance_attribute_points_to(f, value, cls, origin)
}

private predicate final_class_attribute_points_to_impl(AttrNode f, Object value, ClassObject cls, ObjectOrCfg origin_or_obj) {
    f.isLoad() and
    exists(ControlFlowNode fval, string name |
        fval = f.getObject(name) |
        /* The 'obvious' formulation of this:
           exists(ClassObject obj |
              final_points_to(fval, obj, _, _) and
              final_class_attribute_lookup(obj, name, value, cls, origin_or_obj)
           )
         * makes for a very large (and thus slow) recursive layer. So we break the recursion.
         * In order to partially make up for the reduction in accuracy, we use both prev/this and this/prev versions.
         */
        exists(ClassObject obj |
            final_points_to(fval, obj, _, _) and
            penultimate_class_attribute_lookup(obj, name, value, cls, origin_or_obj)
        )
        or
        exists(ClassObject obj |
            penultimate_points_to(fval, obj, _, _) and
            final_class_attribute_lookup(obj, name, value, cls, origin_or_obj)
        )
    )
}

private predicate final_class_attribute_points_to(AttrNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    exists(ObjectOrCfg origin_or_obj |
        final_class_attribute_points_to_impl(f, value, cls, origin_or_obj)
        |
        origin = origin_or_obj
        or
        not origin_or_obj instanceof ControlFlowNode and origin = f
    )
}

private 
ModuleObject final_receiver_module_for(AttrNode f, string name) {
    f.isLoad() and
    exists(ControlFlowNode fval |
        fval = f.getObject(name) |
        final_points_to(fval, result, _, _)
    )
}

pragma [noinline]
private predicate final_receiver_module_for_210(ModuleObject m, string name, AttrNode f) {
    m = final_receiver_module_for(f, name)
}

private 
predicate final_module_attribute_points_to(AttrNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    f.isLoad() and
    exists(ModuleObject obj, string name |
        final_receiver_module_for_210(obj, name, f) |
        exists(ObjectOrCfg origin_or_obj  |
            final_module_attribute_points_to(obj, name, value, cls, origin_or_obj) |
            origin = origin_or_obj.getOrigin()
            or
            not exists(origin_or_obj.getOrigin()) and origin = f
        )
    )
}

/* Helper for instance_attribute_points_to_candidate */
pragma [noinline]
private predicate final_points_to_20(ClassObject cls, Object value) {
    final_points_to(value, _, cls, _)
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
        non_init.getFunction().getScope() = penultimate_get_an_improper_super_type(self_class).getPyClass()
        and
        not penultimate_method_called_from_init(non_init, self_class) 
    )
}

/** Initialization of attribute in the __init__ method or method called by it,
 * provided that the attribute is not stored to outside ne of those functions.
 */
private AttrNode final_initializer_store(ClassObject self_class, string attr_name) {
    result.isStore() 
    and 
    result.getObject(attr_name).getScope().getScope*() = self_class.getPyClass()
    and
    not attr_stored_outside_init(self_class, attr_name)
    and
    exists(FunctionObject init |
        penultimate_method_called_from_init(init, self_class) 
        and
        result.getScope() = init.getFunction()
    )
}

private predicate final_instance_attribute_points_to(ControlFlowNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    /* We are only interested in the simplest attributes here.
     * Defined in initializer exactly and unconditionally once
     */
    /* `f` is `x.attr_name` where `x` is an instance of `self_class` */
    exists(ClassObject self_class, string attr_name |
        exists(ControlFlowNode object |
            not exists(FunctionObject init |
                penultimate_method_called_from_init(init, self_class) and
                final_is_self(object) and
                object.getScope() = init.getFunction()  
            ) and
            final_points_to_20(self_class, object) and
            final_attribute_load_120(object, attr_name, f)
        ) and
        exists(ControlFlowNode store |
            store = final_initializer_store(self_class, attr_name) and
            final_points_to(store.(DefinitionNode).getValue(), value, cls, origin)
        )
    ) and not
    penultimate_attribute_store_load_pair(_, f)
}

/* INTERNAL -- Use FunctionObject.getAMethodCalledFromInit() instead.
 * Whether the function `method` is called, directly or indirectly, from the `__init__` method of owner */
 cached 
predicate final_method_called_from_init(FunctionObject method, ClassObject owner) {
    final_class_attribute_lookup(owner, "__init__", method, _, _)
    or
    exists(FunctionObject caller, CallNode call |
        final_method_called_from_init(caller, owner) and
        call.getScope() = caller.getFunction() and
        dominates_all_normal_exits(call) |
        exists(ControlFlowNode self, AttrNode attr, string name, ClassObject mro_type |
            attr = call.getFunction() and
            final_is_self(self) and
            final_super_call(attr.getObject(name), self, mro_type) and
            penultimate_class_lookup_in_mro(owner, final_next_in_mro(owner, mro_type), name, method)
        )
        or
        exists(AttrNode self_attr, string name |
            call.getFunction() = self_attr and
            final_is_self(self_attr.getObject(name)) |
            final_class_attribute_lookup(owner, name, method, _, _)
        )
    )
}

private predicate final_is_self(NameNode self) {
    final_self_param(self, _)
    or
    exists(SsaVariable self_var |
        final_self_param(self_var.getDefinition(), _) and
        self = self_var.getAUse()
    )
}

private predicate final_if_exp_points_to(IfExprNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    final_points_to(f.getAnOperand(), value, cls, origin)
}

private predicate final_import_points_to(ControlFlowNode f, ModuleObject value, ControlFlowNode origin) {
    exists(string name, ImportExpr i | 
        i.getAFlowNode() = f and i.getImportedModuleName() = name and
        final_module_imported_as(value, name) and
        origin = f
    )
}

private predicate final_from_import_points_to(ImportMemberNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    /* Three options here:
     * 1. We can infer the module's attribute, and that attribute has an origin
     * 2. We can infer the module's attribute, but the attribute has no origin
     * 3. We can't infer the module's attribute.
     */
    exists(ImportMember im, string name |
        im.getAFlowNode() = f and name = im.getName() |
        exists(ModuleObject mod, ObjectOrCfg origin_or_obj |
            final_points_to(f.getModule(name), mod, _, _) and
            final_module_attribute_points_to(mod, name, value, cls, origin_or_obj) |
            origin = origin_or_obj /* 1. */
            or
            not origin_or_obj instanceof ControlFlowNode and origin = f /* 2. */
        )
        or
        not exists(ModuleObject mod | /* 3. */
            penultimate_points_to(f.getModule(name), mod, _, _) and
            penultimate_module_attribute_points_to(mod, name, _, _, _)
        ) and f = origin and value = f and cls = final_global_type(value) 
    )
    and
    /* If locally defined in init, then defer to import time points to */
    not is_locally_defined_from_dot_import_in_init(f, _)
    or
    /* Importing from the package in an __init__ module */
    exists(SsaVariable var | 
        locally_defined_from_dot_import_in_init(f, var) and
        final_ssa_variable_points_to(var, value, cls, origin)
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
            final_ssa_variable_points_to(ssa, value, cls, origin)
        )
        or
        /* Variable is unused except in inner function, so no SSA variable is created */
        not exists(SsaVariable ssa | ssa.getAUse() = f) and
        exists(Variable v | f.uses(v) |
            strictcount(NameNode def | def.defines(v)) = 1 and
            exists(NameNode def | 
                def.defines(v) |
                final_points_to(def, value, cls, origin)
            )
        )
    )
}

/** Whether global variable use `n` refers to `value, cls, origin` and is either a builtin or an import */
private predicate global_builtin_or_import(NameNode n, Object value, ClassObject cls, ControlFlowNode origin) {
   n.isGlobal() 
   and
   not exists(final_get_global_ssa_defn_candidate(_, n))
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
       final_import_star_defines_object(imp, id, value, cls, origin) and
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
       final_ssa_variable_points_to(var, value, cls, origin)
   )
   or
   nonlocal_variable_points_to(n, value, cls, origin)
   or
   final_global_use_points_to(n, value, cls, origin)
   or
   global_builtin_or_import(n, value, cls, origin)
}

/** Get an object pointed to by a use (of a variable) */
private predicate final_use_points_to(NameNode n, Object value, ClassObject cls, ControlFlowNode origin) {
    not final_prohibited_use(n, value, cls) and
    not must_have_boolean_value(n, value.booleanValue().booleanNot()) and
    use_points_to_candidate(n, value, cls, origin)
}

/** Gets an object pointed to by a use with a ssa variable.
 * Note this can be a local variable in a function or class or a global variable at module scope */
pragma [nomagic]
private predicate final_ssa_variable_points_to(SsaVariable var, Object value, ClassObject cls, ControlFlowNode origin) {
    final_points_to(var.getDefinition(), value, cls, origin) and not exists(var.getAPhiInput())
    or
    final_ssa_phi_points_to(var, value, cls, origin)
}

/** What the the SSA variable 'var' may point to, provided that it is a phi node, taking care to account 
 * for guards on the incoming edges. The points-to relation for an SSA phi-node is the union of its incoming 
 * SSA variables, excepting those values and classes that are explicitly guarded against.
 */
private predicate final_ssa_phi_points_to(SsaVariable var, Object value, ClassObject cls, ControlFlowNode origin) {
    exists(SsaVariable incoming, BasicBlock pred, BasicBlock succ |
        pred = var.getPredecessorBlockForPhiArgument(incoming) and succ = var.getDefinition().getBasicBlock() |
        not final_prohibited_on_edge(incoming, pred, succ, value, cls) and
        not must_have_boolean_value_on_edge(incoming, pred, succ, value.booleanValue().booleanNot()) and
        final_ssa_variable_points_to(incoming, value, cls, origin)
    )
}

/** Gets an object pointed to by this definition */
private predicate final_def_points_to(ControlFlowNode n, Object value, ClassObject cls, ControlFlowNode origin) {
    final_points_to(n.(DefinitionNode).getValue(), value, cls, origin)
    or
    /* Default values for parameters */
    n.isParameter() and 
    exists(Parameter p | 
        p.asName().getAFlowNode() = n and 
        final_points_to(p.getDefault().getAFlowNode(), value, cls, origin) 
    )
    or
    /* General parameters, including those with defaults. */
    n.isParameter() and not penultimate_self_param(n, _) and value = n and origin = n and cls = theUnknownType()
    or
    exists(FunctionObject meth | final_self_param(n, meth) and final_self_type(meth, cls)) and value = n and origin = n
}

predicate final_abstract_class(ClassObject cls) {
    final_class_explicit_metaclass(cls) = theAbcMetaClassObject()
    or
    exists(string name, FunctionObject unimplemented, Raise r |
        final_class_attribute_lookup(cls, name, unimplemented, _, _) and
        r.getScope() = unimplemented.getFunction() and
        (
            final_points_to(r.getException().getAFlowNode(), theNotImplementedErrorType(), _, _)
            or
            final_points_to(r.getException().getAFlowNode(), _, theNotImplementedErrorType(), _)
        )
    )
}

predicate final_concrete_class(ClassObject cls) {
    final_instantiation(_, cls)
    or
    not penultimate_abstract_class(cls)
}

/** Whether `cls` is a possible class of self in `method` */
/* This is public mainly for testing */
predicate final_self_type(FunctionObject method, ClassObject cls) {
    (
        final_concrete_class(cls)
        or
        method.getFunction().getScope() = cls.getPyClass()
    )
    and
    (
        /* Standard call */
        final_class_attribute_lookup(cls, _, method, _, _)
        or
        /* Call via super */
        final_super_method_call(_, cls, method)
    )
}

private predicate final_subscript_load_store_pair(SubscriptNode store, SubscriptNode load) {
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
        final_points_to(store.getIndex(), index, _, _) and
        final_points_to(load.getIndex(), index, _, _)
    )
}

/** Gets an object pointed to by this subscript load */
private predicate final_subscript_points_to(SubscriptNode f, Object value, ClassObject cls, ControlFlowNode origin) {
    exists(SubscriptNode store |
        final_subscript_load_store_pair(store, f) |
        final_points_to(store.(DefinitionNode).getValue(), value, cls, origin)
    )
}

/** Whether `call` is a call to super() with for an object of class `self_type`
 * and the `start` class in the MRO. E.g
 * For a call `super(T, self)`. 
 * `self_type` is `type(self)` and `start` is `T`
 * Handles both Python 2 style `super(T, self)` and Python 3 style `super()`.
 */
 /* This might need to be part of public API */
private predicate final_super_call_types(CallNode call, ClassObject self_type, ClassObject start_type) {
    exists(ClassObject mro_type, ControlFlowNode self |
        start_type = final_next_in_mro(self_type, mro_type) and
        final_super_call(call, self, mro_type) and
        final_points_to_20(self_type, self)
    )
}

/* INTERNAL -- Public for testing only */
predicate final_super_call(CallNode call, ControlFlowNode self, ClassObject mro_type) {
    penultimate_points_to(call.getFunction(), theSuperType(), _, _) and
    (
        penultimate_points_to(call.getArg(0), mro_type, _, _) and
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
predicate final_super_method_call(CallNode call, ClassObject self_type, FunctionObject method) {
    exists(AttrNode attr |
        attr = call.getFunction() and
        exists(CallNode super_call, ClassObject start_type, string name |
            // lifted to help join-ordering
            final_super_method_call_helper(attr, self_type, super_call, start_type, name) and
            /* super().name lookup */
            final_class_lookup_in_mro(self_type, start_type, name, method)
        )
    )
}

pragma[noinline]
private predicate final_super_method_call_helper(AttrNode attr, ClassObject self_type, CallNode super_call, ClassObject start_type, string name) {
    final_super_call_types(super_call, self_type, start_type) and 
    penultimate_points_to(attr.getObject(name), super_call, _, _)
}

/** INTERNAL -- Do not use */
predicate final_attribute_store(SsaVariable var, string name, ControlFlowNode stored) {
    last_simple_attribute_store_in_scope(var, name, stored)
    or
    extensional_name(name) and
    exists(CallNode call |
        /* This must be part of the previous layer, to prevent incorrect join ordering */
        penultimate_points_to(call.getFunction(), builtin_object("setattr"), _, _) and
        var.getAUse() = call.getArg(0) and
        call.getArg(1).getNode().(StrConst).getText() = name and
        call.getArg(2) = stored
    )
}

/* A load of an attribute, either directly or through getattr,
 * `objectuse` is the use of the object with attribute `name`
 */
/** INTERNAL -- Do not use */
predicate final_attribute_load(ControlFlowNode load, ControlFlowNode objectuse, string name) {
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
        penultimate_points_to(call.getFunction(), builtin_object("getattr"), _, _) and
        objectuse = call.getArg(0) and
        call.getArg(1).getNode().(StrConst).getText() = name
    )
  )
}

pragma [noinline]
private predicate final_attribute_load_120(ControlFlowNode objectuse, string name, ControlFlowNode load) {
     final_attribute_load(load, objectuse, name)
}

private predicate final_self_attribute_store_in_block(BasicBlock b, string attrname, ControlFlowNode stored) {
    extensional_name(attrname) and
    exists(SsaVariable var |
       final_attribute_store(var, attrname, stored) and
       var.isSelf()
    ) and
    stored.getBasicBlock() = b
}

private predicate final_self_attribute_set_in_block(BasicBlock b, string attrname, ControlFlowNode stored) {
    final_self_attribute_store_in_block(b, attrname, stored)
    or
    final_self_attribute_set_in_block(b.getAPredecessor(), attrname, stored)
}

private predicate final_self_attribute_not_set_in_block(BasicBlock b, string attrname) {
    exists(BasicBlock other |
        b.getScope() = other.getScope() |
        final_self_attribute_set_in_block(other, attrname, _)
    )
    and
    not final_self_attribute_store_in_block(b, attrname, _)
    and
    (
        not final_self_attribute_set_in_block(b, attrname, _)
        or
        final_self_attribute_not_set_in_block(b.getAPredecessor(), attrname)
    )
}

/** INTERNAL -- Use `FunctionObject.unconditionallySetsSelfAttribute(attrname)` instead */
 cached 
predicate final_unconditionally_sets_self_attribute(FunctionObject method, string attrname) {
    extensional_name(attrname) and
    forex(BasicBlock exit |
        exit.getLastNode() = method.getFunction().getANormalExit() |
        final_self_attribute_set_in_block(exit, attrname, _) and
        not final_self_attribute_not_set_in_block(exit, attrname)
    )
}

private predicate final_sets_self_attribute(FunctionObject method, string attrname, ControlFlowNode store) {
    exists(BasicBlock b |
        final_self_attribute_set_in_block(b, attrname, store) |
        b.getLastNode() = method.getFunction().getANormalExit()
    )
}

private predicate final_assigned_in_init(ClassObject cls, string name) {
    exists(FunctionObject init |
        final_class_attribute_lookup(cls, "__init__", init, _, _) and
        final_sets_self_attribute(init, name, _)
    )
}

/** INTERNAL -- Do not use */
predicate final_call_sets_self_attribute(CallNode call, SsaVariable var, string attrname, ControlFlowNode store) {
    extensional_name(attrname) and
    exists(FunctionObject method |
        /* `method` is called by `call` with `var` as the 'self' argument */
        final_self_method_call(method, call, var) and
        final_sets_self_attribute(method, attrname , store)
    )
}

private predicate final_self_method_call(FunctionObject method, CallNode call, SsaVariable self) {
    self.isSelf() and
    call.getFunction().(AttrNode).getObject() = self.getAUse() and
    call = final_get_a_call(method)
}

/** INTERNAL -- Use  ClassObject.getBaseType(n) instead.
 * Gets the nth base class of the class */
 cached 
Object final_class_base_type(ClassObject cls, int n) {
    exists(ClassExpr cls_expr | cls.getOrigin() = cls_expr |
        final_points_to(cls_expr.getBase(n).getAFlowNode(), result, _, _)
        or
        final_is_new_style(cls) and not exists(cls_expr.getBase(0)) and result = theObjectType() and n = 0
    )
    or
    result = builtin_base_type(cls) and n = 0
}

/** INTERNAL -- Use ClassObject.isNewStyle() instead. */
 cached 
predicate final_is_new_style(ClassObject cls) {
    cls.isC()
    or
    major_version() >= 3
    or
    exists(cls.declaredMetaClass())
    or
    final_is_new_style(final_class_base_type(cls, _))
}

/** INTERNAL -- Do not use */
predicate final_mro_sparse(ClassObject cls, ClassObject sup, int index) {
    if final_is_new_style(sup) then (
        final_depth_first_indexed(cls, sup, index) and
        not exists(int after | final_depth_first_indexed(cls, sup, after) and after > index)
    ) else (
        final_depth_first_indexed(cls, sup, index) and
        not exists(int before | final_depth_first_indexed(cls, sup, before) and before < index)
    )
}

/** An index for the base class in the mro such that the index for superclasses of the base
 * class are guaranteed not to clash with the superclasses of other base classes.  */
private predicate final_class_base_offset(ClassObject cls, ClassObject base, int index) {
    exists(int n |
        final_class_base_type(cls, n) = base |
        index = sum(ClassObject left_base |
            exists(int i | left_base = final_class_base_type(cls, i) and i < n) |
            count (final_get_an_improper_super_type(left_base))
        )
    )
}

/** Index all super-classes using depth-first search, 
 * numbering parent nodes before their children */
private predicate final_depth_first_indexed(ClassObject cls, ClassObject sup, int index) {
    not final_has_illegal_bases(cls) and final_get_an_improper_super_type(cls) = sup and
    (
        sup = cls and index = 0
        or
        exists(ClassObject base, int base_offset, int sub_index |
            base = final_class_base_type(cls, _) and
            final_class_base_offset(cls, base, base_offset) and
            final_depth_first_indexed(base, sup, sub_index) and
            index = base_offset + sub_index + 1
        )
    )
}

/** INTERNAL -- Use ClassObject.getASuperType() instead */
 cached 
ClassObject final_get_a_super_type(ClassObject cls) {
    result = final_class_base_type(cls, _)
    or
    result = final_class_base_type(final_get_a_super_type(cls), _)
}

/** INTERNAL -- Use ClassObject.getAnImproperSuperType() instead */
 cached 
ClassObject final_get_an_improper_super_type(ClassObject cls) {
    result = cls
    or
    result = final_get_a_super_type(cls)
}


/** This class has duplicate base classes */
private predicate final_has_duplicate_bases(ClassObject cls) {
    exists(ClassObject base, int i, int j | i != j and base = final_class_base_type(cls, i) and base = final_class_base_type(cls, j))
}

private predicate final_has_illegal_bases(ClassObject cls) {
    final_has_duplicate_bases(cls) or final_get_an_improper_super_type(final_class_base_type(cls, _)) = cls
}

/** INTERNAL -- Use ClassObject.getMroItem(index) instead */

 cached 
ClassObject final_get_mro_item(ClassObject cls, int index) {
        /* Collapse the sparse array into a dense one */
        exists(int idx | penultimate_mro_sparse(cls, result, idx) |
            idx = rank[index](int i, ClassObject s | penultimate_mro_sparse(cls, s, i) | i)
        )
}

/** INTERNAL -- ClassObject.nextInMro(sup) instead */
 cached 
ClassObject final_next_in_mro(ClassObject cls, ClassObject sup) {
    exists(int i |
        sup = final_get_mro_item(cls, i) and
        result = final_get_mro_item(cls, i+1)
    )
}

private int final_declaring_class_index(ClassObject cls, string name) {
    class_declares_attribute(final_get_mro_item(cls, result), name)
}

/** INTERNAL -- ClassObject.lookupMro(start, name) instead */
pragma [nomagic]
 cached 
predicate final_class_lookup_in_mro(ClassObject cls, ClassObject start, string name, Object object) {
    extensional_name(name) and
    exists(int i, int j |
        start = final_get_mro_item(cls, i) and
        j = final_declaring_class_index(cls, name) and j >= i and 
        not exists(int k | k = final_declaring_class_index(cls, name) and k >= i and k < j) and
        final_class_declared_attribute(final_get_mro_item(cls, j), name, object, _, _)
    )
}

/** INTERNAL -- Use ClassObject.declaredAttribute(name) instead */
 cached 
predicate final_class_declared_attribute(ClassObject cls, string name, Object value, ClassObject vcls, ObjectOrCfg origin) {
    extensional_name(name) and
    (
      final_object_defined_at_scope_exit(cls.getImportTimeScope(), name, value, vcls, origin)
      or
      value = builtin_class_attribute(cls, name) and class_declares_attribute(cls, name) and 
      origin = value and vcls = builtin_object_type(value)
   )
}

/** INTERNAL -- Use ClassObject.hasAttribute(name) instead */
 cached 
predicate final_class_has_attribute(ClassObject cls, string name) {
    extensional_name(name) and
    class_declares_attribute(final_get_an_improper_super_type(cls), name)
}

pragma [nomagic]
private ClassObject final_class_supertype_declaring_attr(ClassObject cls, string name) {
    exists(int i |
        i = min(int j | class_declares_attribute(final_get_mro_item(cls, j), name)) |
        result = final_get_mro_item(cls, i)
    )
}

/** INTERNAL -- Use ClassObject.attributeRefersTo(name, vlaue, vlcs, origin) instead
 */
pragma [nomagic]
 cached 
predicate final_class_attribute_lookup(ClassObject cls, string name, Object value, ClassObject vcls, ObjectOrCfg origin) {
     extensional_name(name) and
   /* Choose attribute declared in (super)class  closest to start of MRO. */
    final_class_declared_attribute(final_class_supertype_declaring_attr(cls, name), name, value, vcls, origin)
}

/** INTERNAL -- Use ClassObject.getMetaClass() instead.
 *  Gets the metaclass for this class */
 cached 
ClassObject final_class_get_meta_class(ClassObject cls) {
    penultimate_has_explicit_metaclass(cls) and result = final_class_explicit_metaclass(cls)
    or
    /* Meta class determination http://gnosis.cx/publish/programming/metaclass_2.html */
    not penultimate_has_explicit_metaclass(cls) and result = final_inherited_metaclass(cls)
    or
    /* No declared or inherited metaclass */
    not penultimate_has_explicit_metaclass(cls) and not cls.hasABase()
    and 
    ( if baseless_is_new_style(cls) then
          result = theTypeType()
      else
          result = theClassType()
    )
}

/** INTERNAL -- Do not use */
predicate final_has_explicit_metaclass(ClassObject cls) {
    exists(final_class_explicit_metaclass(cls))
}

/** INTERNAL -- Do not use */
ClassObject final_class_explicit_metaclass(ClassObject cls) {
    final_points_to(cls.declaredMetaClass(), result, _, _)
    or
    py_cobjecttypes(cls, result) and is_c_metaclass(result)
    or
    exists(ControlFlowNode meta |
        penultimate_six_add_metaclass(_, cls, meta) and
        final_points_to(meta, result, _, _)
    )
}

private ClassObject final_inherited_metaclass(ClassObject cls) {
    result = final_class_explicit_metaclass(final_get_a_super_type(cls))
    and
    forall(ClassObject possibleMeta | 
        possibleMeta = penultimate_class_explicit_metaclass(penultimate_get_a_super_type(cls)) |
        final_get_an_improper_super_type(result) = possibleMeta
    )
}

/* INTERNAL -- Do not use */
FunctionObject final_six_add_metaclass_function() {
    exists(ModuleObject six |
        six.getName() = "six" and
        final_module_attribute_points_to(six, "add_metaclass", result, _, _)
    )
}

/* INTERNAL -- Do not use */
predicate final_six_add_metaclass(CallNode decorator_call, ClassObject decorated, ControlFlowNode metaclass) {
    exists(CallNode decorator |
        decorator_call.getArg(0) = decorated and
        decorator = decorator_call.getFunction() |
        final_points_to(decorator.getFunction(), final_six_add_metaclass_function(), _, _) and
        decorator.getArg(0) = metaclass
    )
}


/** INTERNAL -- Use ClassObject.failedInference(reason) instead.
 *  Has type inference failed to compute the full class hierarchy for this class for the reason given. */ 
 cached 
predicate final_failed_inference(ClassObject cls, string reason) {
    strictcount(cls.getPyClass().getADecorator()) > 1 and reason = "Multiple decorators"
    or
    exists(cls.getPyClass().getADecorator()) and not final_six_add_metaclass(_, cls, _) and reason = "Decorator not understood"
    or
    exists(int i | exists(cls.getOrigin().(ClassExpr).getBase(i)) and not exists(penultimate_class_base_type(cls, i)) and reason = "Missing base " + i)
    or
    /* Base class is not something we can understand as a class */
    exists(int i |
        exists(cls.getOrigin().(ClassExpr).getBase(i)) |
        exists(Object b | b = final_class_base_type(cls, i) and not b instanceof ClassObject) and reason = "Base " + i + " is not a simple class"
    )
    or
    exists(cls.getPyClass().getMetaClass()) and not penultimate_has_explicit_metaclass(cls) and reason = "Failed to infer metaclass"
    or
    exists(int i | final_failed_inference(final_class_base_type(cls, i), _) and reason = "Failed inference for base class at position " + i)
    or
    exists(int i | strictcount(penultimate_class_base_type(cls, i)) > 1 and reason = "Multiple bases at position " + i)
}

/** INTERNAL -- Do not use */
pragma [nomagic]
predicate final_module_attribute_points_to(ModuleObject mod, string name, Object value, ClassObject cls, ObjectOrCfg origin) {
    extensional_name(name) and
    (
      final_py_module_attributes(mod.getModule(), name, value, cls, origin)
      or
      final_package_attributes(mod, name, value, cls, origin)
      or
      value = builtin_module_attribute(mod, name) and cls = builtin_object_type(value) and origin = value
    )
}

/** INTERNAL -- Use m.attributeRefersTo(name, obj, origin) instead */
 cached 
predicate final_py_module_attributes_explicit(Module m, string name, Object obj, ClassObject cls, ControlFlowNode origin) {
    not m.isPackage() and extensional_name(name) and
    (
      exists(SsaVariable var | var.getAUse() = m.getANormalExit() and var.getId() = name |
          final_ssa_variable_points_to(var.getAnUltimateDefinition(), obj, cls, origin)
      )
      or
      final_import_star_defines_object_in_module(m, name, obj, cls, origin)
      or
      exists(DefinitionNode def,  GlobalVariable v |
          v.getScope() = m and v.getId() = name and
          def = final_get_global_ssa_defn_at_scope_end(v, m) and
          final_points_to(def, obj, cls, origin)
      )
    )
}

/** INTERNAL -- Use m.attributeRefersTo(name, obj, origin) instead */
 cached 
predicate final_py_module_attributes(Module m, string name, Object obj, ClassObject cls, ControlFlowNode origin) {
    not m.isPackage() and extensional_name(name) and
    (
      final_py_module_attributes_explicit(m, name, obj, cls, origin)
      or
      not penultimate_py_module_attributes_explicit(m, "__name__", _, _, _) and cls = theStrType() and
      name = "__name__" and obj = object_for_string(m.getName()) and origin = m.getEntryNode()
      or
      /* Set the __package__ to the value specified in the documentation.
       * Note, however, that it is often None in practice as the interpreter sets 
       * the __package__ attribute only when required by the import machinery.
       * We choose the string value in preference to None as it is the steady state value.  
       */
      not penultimate_py_module_attributes_explicit(m, "__package__", _, _, _) and name = "__package__" and cls = theStrType() and 
      obj = object_for_string(m.getPackage().getName()) and origin = m.getEntryNode()
    )
}

/** INTERNAL -- Use package.attributeRefersTo(name, obj, origin) instead */
 cached 
predicate final_package_attributes(PackageObject package, string name, Object obj, ClassObject cls, ControlFlowNode origin) {
    extensional_name(name) and (
      not name = "__name__" and final_module_attribute_points_to(package.getInitModule(), name, obj, cls, origin)
      or
      name = "__name__" and obj = object_for_string(package.getName()) and origin = package.getModule().getEntryNode() and cls = theStrType()
      or
      not penultimate_py_module_attributes_explicit(package.getInitModule().getModule(), "__package__", _, _, _) and
      name = "__package__" and obj = object_for_string(package.getName()) and origin = package.getModule().getEntryNode() and cls = theStrType()
      or
      not final_module_defines_name(package.getInitModule().getModule(), name)
      and
      exists(ModuleObject mod |
          mod.getModule() = package.getModule().getSubModule(name) and
          origin = mod.getModule().getEntryNode() and
           obj = mod and
          final_explicitly_imported(mod) and
          cls = theModuleType()
      )
    )
}

/** Whether the module is explicitly imported somewhere */
private predicate final_explicitly_imported(ModuleObject mod) {
    exists(ImportExpr ie | final_module_imported_as(mod, ie.getAnImportedModuleName()))
    or
    exists(ImportMember im | final_module_imported_as(mod, im.getImportedModuleName()))
}

/** Return the Object(s) which can be bound to 'name' upon completion of the code defining this namespace */
private predicate final_object_defined_at_scope_exit(ImportTimeScope scope, string name, Object value, ClassObject cls, ControlFlowNode origin) {
    exists(SsaVariable var | var.getAUse() = scope.getANormalExit() and var.getId() = name |
        final_ssa_variable_points_to(var.getAnUltimateDefinition(), value, cls, origin)
    )
    or
    final_import_star_defines_object_in_module(scope, name, value, cls, origin)
}

/** INTERNAL -- Use ModuleObject.hasAttribute(name)
 *  Whether the module defines name */
 cached 
predicate final_module_defines_name(Module mod, string name) {
    extensional_name(name) and
    (
        exists(SsaVariable var | name = var.getId() and var.getAUse() = mod.getANormalExit())
        or
        final_import_star_defines_name(mod, name)
    )
}

/* Public API -- Used by UndefinedGlobal query. */
 cached 
predicate final_import_star_defines_name(Module m, string name) {
    extensional_name(name) and
    exists(ModuleObject imported_module, ImportStar import_stmt |
        final_has_import_star(m, import_stmt, imported_module)
        |
        final_module_exports(imported_module.getModule(), name)
        or
        exists(builtin_module_attribute(imported_module, name))
    )
}

private 
predicate final_import_star_defines_object(ImportStarNode star, string name, Object obj, ClassObject cls, ControlFlowNode origin) {
    extensional_name(name) and
    exists(ModuleObject imported_module |
        /* This is a relatively unimportant way of defining of defining values and breaking the 
         * recursion here gives a big speed up.
         */
        penultimate_points_to(star.getModule(), imported_module, _, _) |
        penultimate_module_exports(imported_module.getModule(), name) and
        penultimate_module_attribute_points_to(imported_module, name, obj, cls, origin)
        or
        origin = star and obj = builtin_module_attribute(imported_module, name) and cls = builtin_object_type(obj)
    )
}

private 
predicate final_import_star_defines_object_in_module(ImportTimeScope scope, string name, Object obj, ClassObject cls, ControlFlowNode origin) {
    extensional_name(name) and
    exists(ImportStarNode import_star |
        import_star.getScope() = scope and
        final_import_star_defines_object(import_star, name, obj, cls, origin)
    )
}

/** INTERNAL -- Use m.exports(name) instead */
 cached 
predicate final_module_exports(Module m, string name) {
    extensional_name(name) and
    if m.isPackage() then (
        not m.getInitModule().declaredInAll(_) and not name.charAt(0) = "_" and
        exists(ModuleObject sub |
            sub.getModule() = m.getSubModule(name) |
            final_explicitly_imported(sub)
        )
        or
        final_module_exports(m.getInitModule(), name)
    ) else (
        m.declaredInAll(_) and m.declaredInAll(name)
        or
        not m.declaredInAll(_) and final_module_defines_name(m, name) and not name.charAt(0) = "_"
    )
}

/** Does an import star exists in Module m that imports a module called 'name', such that the flow from the import reached the module exit. */
private predicate final_has_import_star(Module m, ImportStar im, ModuleObject imported_module) {
    exists(string name |
        final_module_imported_as(imported_module, name) and
        name = im.getImportedModuleName() and
        im.getScope() = m and
        im.getAFlowNode().getBasicBlock().reachesExit()
    )
}

/** INTERNAL -- Use m.importedAs(name) instead */
 cached 
predicate final_module_imported_as(ModuleObject m, string name) {
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
            penultimate_points_to(sys_modules_flow, sys_modules, _, _) and
            sys_modules = builtin_module_attribute(theSysModuleObject(), "modules") and
            sub.getIndex() = n and
            n.getNode().(StrConst).getText() = name and
            sub.(DefinitionNode).getValue() = mod and
            penultimate_points_to(mod, m, _, _)
        )
      )
    )
}


/********************
 * VERSION INFO
 */

private predicate final_sys_version_info_index(SubscriptNode s) {
    final_points_to_10(theSysVersionInfoTuple(), s.getValue()) and
    exists(NumericObject zero |
        zero.intValue() = 0 |
        final_points_to(s.getIndex(), zero, _, _)
    )
}

private predicate final_sys_version_info_slice(SubscriptNode s) {
    final_points_to_10(theSysVersionInfoTuple(), s.getValue()) and
    exists(Slice index | index = s.getIndex().getNode() |
        not exists(index.getStart())
    )
}

pragma[noinline]
private predicate final_points_to_10(Object value, ControlFlowNode f) {
    final_points_to(f, value, _, _)
}

private predicate final_comparison(CompareNode cmp, ControlFlowNode fv, ControlFlowNode fc, string opname) {
    exists(Cmpop op |
        cmp.operands(fv, op, fc) and opname = op.getSymbol()
        or
        cmp.operands(fc, op, fv) and opname = reversed(op)
    )
}

/** INTERNAL -- Use Version.getVersion() instead */
 cached 
predicate final_version_test(CompareNode cmp, Version v) {
    exists(ControlFlowNode fv, ControlFlowNode fc, string opname, int n |
        final_comparison(cmp, fv, fc, opname) and
        version_compare(v, n, opname)
        |
        exists(Object vobj, Object const |
            final_points_to(fv, vobj, _, _) and
            final_points_to(fc, const, _, _)
            |
            final_sys_version_info_index(vobj) and n = const.(NumericObject).intValue()*16
            or
            n = version_tuple_value(const) and
            (final_sys_version_info_slice(vobj) or vobj = theSysVersionInfoTuple())
            or
            vobj = theSysHexVersionNumber() and
            n = scale_hex_version(const.(NumericObject).intValue())
        )
    )
}

private predicate final_os_test(ControlFlowNode f, string os) {
    exists(ControlFlowNode c |
         os_compare(c, os) and
         final_points_to(f, _, _, c)
    )
}

private predicate final_boolean_const(ControlFlowNode f, boolean value) {
    exists(Version v, Object test |
        final_points_to(f, test, _, _) and final_version_test(test, v) |
        value = true and v = major_version()
        or
        value = false and v != major_version()
    )
    or
    exists(string os |
        final_os_test(f, os) |
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
        final_ssa_boolean_const(var, value)
    )
    or
    exists(ModuleObject mod, string name |
        final_points_to(f.(AttrNode).getObject(name), mod, _, _) and 
        final_attribute_boolean_const(mod, name, value)
    )
}

private predicate final_ssa_boolean_const(SsaVariable var, boolean value) {
    final_boolean_const(var.getDefinition().(DefinitionNode).getValue(), value)
    or
    forex(SsaVariable input |
        input = var.getAPhiInput() |
        final_ssa_boolean_const(input, value)
    )
    or
    exists(ConditionBlock guard, boolean sense |
        final_boolean_const(guard.getLastNode(), sense) |
        exists(SsaVariable in1 |
            in1 = var.getAPhiInput() |
            guard.controls(in1.getDefinition().getBasicBlock(), sense) and final_ssa_boolean_const(in1, value)
            or
            /* Oh why do I still need to do this? */
            (value = true or value = false) and
            guard.controls(in1.getDefinition().getBasicBlock(), sense.booleanNot()) and final_ssa_boolean_const(in1, value.booleanNot())
        )
    )
}

private predicate final_attribute_boolean_const(ModuleObject mod, string name, boolean value) {
    exists(SsaVariable var | var.getAUse() = mod.getModule().getANormalExit() and var.getId() = name |
        final_ssa_boolean_const(var, value)
    )
}


/** INTERNAL -- Whether this ControlFlowNode is pruned due to version or OS constraints. */
predicate final_pruned(ControlFlowNode f) {
    exists(ConditionBlock guard |
        guard.controls(f.getBasicBlock(), true) and final_boolean_const(guard.getLastNode(), false)
        or
        guard.controls(f.getBasicBlock(), false) and final_boolean_const(guard.getLastNode(), true)
    )
}


/* Function related points-to. This needs to be here rather than in FunctionObject, as
 * it may be required by points-to extensions.
 */

/** INTERNAL -- Use FunctionObject.neverReturns() instead.
 *  Whether function `func` never returns. Slightly conservative approximation, this predicate may be false
 * for a function that can never return. */
  cached 
predicate final_function_never_returns(FunctionObject func) {
    /* A Python function never returns if it has no normal exits that are not dominated by a
     * call to a function which itself never returns.
     */
        exists(Function f | f = func.getFunction() |
        not exists(ControlFlowNode exit |
            exit = f.getANormalExit()
            and
            not exists(FunctionObject callee, BasicBlock call  |
                final_get_a_call(callee).getBasicBlock() = call and
                final_function_never_returns(callee) and
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
 cached 
CallNode final_get_a_call(FunctionObject func) {
    final_function_call(func, result)
    or
    final_method_call(func, result)
}

/** INTERNAL -- Use FunctionObject.getAFunctionCall() */
 cached 
predicate final_function_call(FunctionObject func, CallNode call) {
    final_points_to(call.getFunction(), func, _, _)
}

/** INTERNAL -- Use FunctionObject.getAMethodCall() */
pragma [nomagic]
 cached 
predicate final_method_call(FunctionObject func, CallNode call) {
    exists(ControlFlowNode attr, ClassObject cls, string name |
        attr = call.getFunction() and
        final_receiver_type_for(cls, name, attr) and
        final_class_attribute_lookup(cls, name, func, _, _)
    )
    or
    final_super_method_call(call, _, func)
}

/** INTERNAL -- Do not use. This is part of the internal API.
 * Whether cls `cls` is the receiver type of an attribute access `n`.
 *  Also bind the name of the attribute.
 */
 cached 
predicate final_receiver_type_for(ClassObject cls, string name, ControlFlowNode n) {
  extensional_name(name) and
  (
    /* `super().meth()` is not a method on `super` */
    cls != theSuperType() and
    exists(Object o |
        /* list.__init__() is not a call to type.__init__() */
        not o instanceof ClassObject |
        final_points_to(n.(AttrNode).getObject(name), o, cls, _)
    )
    or
    exists(PlaceHolder p, Variable v | 
        n.getNode() = p and n.(NameNode).uses(v) and name = v.getId() and
        p.getScope().getScope() = cls.getPyClass()
    )
  )
}

pragma [nomagic]
private ControlFlowNode final_get_argument_for_call_by_position(FunctionObject func, CallNode call, int position) {
    final_method_call(func, call) and
    (
        result = call.getArg(position-1)
        or
        position = 0 and result = call.getFunction().(AttrNode).getObject()
    )
    or
    final_function_call(func, call) and
    result = call.getArg(position)
}

private predicate keyword_value_for_call(CallNode call, string name, ControlFlowNode value) {
    exists(Keyword kw |
        call.getNode().getAKeyword() = kw |
        kw.getArg() = name and kw.getValue() = value.getNode() and
        value.getBasicBlock().dominates(call.getBasicBlock())
    )
}

private ControlFlowNode final_get_argument_for_call_by_name(FunctionObject func, CallNode call, string name) {
    call = final_get_a_call(func) and 
    keyword_value_for_call(call, name, result)
}

/** INTERNAL -- Use FunctionObject.getArgumentForCall(call, position) instead.  */
 cached 
ControlFlowNode final_get_positional_argument_for_call(FunctionObject func, CallNode call, int position) {
    result = final_get_argument_for_call_by_position(func, call, position)
    or
    exists(string name |
        result = final_get_argument_for_call_by_name(func, call, name) and
        func.getFunction().getArg(position).asName().getId() = name
    )
}

/** INTERNAL -- Use FunctionObject.getNamedArgumentForCall(call, name) instead.  */
 cached 
ControlFlowNode final_get_named_argument_for_call(FunctionObject func, CallNode call, string name) {
  extensional_name(name) and
  (
    result = final_get_argument_for_call_by_name(func, call, name)
    or
    exists(int position |
        result = final_get_argument_for_call_by_position(func, call, position) and
        func.getFunction().getArg(position).asName().getId() = name
    )
  )
}

/**
 * Whether this implictly returns an object
 */
private predicate final_implicitly_returns(PyFunctionObject func, Object none_, ClassObject noneType) {
   noneType = theNoneType() and not func.getFunction().isGenerator() and none_ = theNoneObject() and
   (
     not exists(func.getAReturnedNode()) and exists(func.getFunction().getANormalExit())
     or
     exists(Return ret | ret.getScope() = func.getFunction() and not exists(ret.getValue()))
   )
}

/** INTERNAL -- Use FunctionObject.getAnInferredReturnType() instead.  */
 cached 
ClassObject final_get_an_inferred_return_type(FunctionObject func) {
     func.getFunction().isGenerator() and result = theGeneratorType()
     or
     not penultimate_function_never_returns(func) and not func.getFunction().isGenerator() and
     (
       final_points_to(func.(PyFunctionObject).getAReturnedNode(), _, result, _)
       or
       final_implicitly_returns(func, _, result)
       or 
       /* If the origin of the the return node is a call to another function, then this function will return the type of that call 
        * Note: since runtime_points_to() is intra-procedural, we need to handle the return types of calls explicitly here. */
       exists(FunctionObject callee |
           final_points_to(func.(PyFunctionObject).getAReturnedNode(), _, theUnknownType(), callee.getACall()) |
           result = final_get_an_inferred_return_type(callee)
       )
     )
     or
     result = func.(BuiltinCallable).getAReturnType()
}

FunctionObject final_get_a_callee(Scope s) {
    exists(ControlFlowNode node |
        node.getScope() = s and
        node = final_get_a_call(result)
    )
}

// Helper for scope_precedes
private predicate final_scope_executes(Scope caller, Scope callee, ControlFlowNode exec) {
    exists(FunctionObject f |
        caller = exec.getScope() and f.getFunction() = callee and exec = penultimate_get_a_call(f)
    )
    or
    caller = exec.getScope() and
    exec.getNode().(ClassExpr).getInnerScope() = callee
}

// Helper for scope_precedes
private predicate final_scope_calls(Scope caller, Scope callee) {
    final_scope_executes(caller, callee, _)
    or
    exists(Scope mid |
        final_scope_calls(mid, callee) and
        final_scope_calls(caller, mid)
    )
}

// Temporal scope ordering.
predicate final_scope_precedes(Scope pre, Scope post, int ranking) {
    not final_scope_calls(pre, post) and
    not final_scope_calls(post, pre) and
    base_scope_precedes(pre, post, ranking)
}

/** Do not use -- For testing purposes */
predicate final_global_phi_definition(GlobalVariable v, BasicBlock phi) {
    exists(BasicBlock x, ControlFlowNode defnode | 
        defnode = x.getNode(_) and
        x.dominanceFrontier(phi) and final_global_ssa_defn(v, defnode, _)
    )
}

/** Whether scope `s` uses`v` either directly in one of its callees. */
private predicate final_scope_uses_global(GlobalVariable v, Scope s) {
    v.getALoad().getScope() = s
    or
    exists(Function callee |
        penultimate_get_a_callee(s).getFunction() = callee and
        final_scope_uses_global(v, callee)
   )
}

/** Whether scope `s` defines `v` either directly in one of its callees. */
private predicate final_scope_defines_global(GlobalVariable v, Scope s) {
    v.getAStore().getScope() = s
    or
    exists(Function callee |
        penultimate_get_a_callee(s).getFunction() = callee and
        final_scope_defines_global(v, callee)
   )
}

/** Do not use -- For testing only.
 * Whether scope `pre` pre-defines `v` for the global-SSA variable `(v, entry)` where `entry` is the entry point to a scope.
 */
predicate final_global_prev_scope(GlobalVariable v, ControlFlowNode entry, Scope pre) {
    exists(Scope post |
        post.getEntryNode() = entry and
        final_scope_uses_global(v, post) and
        exists(final_get_global_ssa_defn_at_scope_end(v, pre)) |
        final_scope_precedes(pre, post, 1) or
        final_scope_precedes(pre, post, 2) and
        not exists(Scope better, ControlFlowNode defn |
            defn.getScope() = better and
            final_scope_precedes(better, post, 1) and
            penultimate_global_ssa_defn(v, defn, _)
        )
    )
}

pragma [noopt]
private predicate final_global_defn_from_callsite(GlobalVariable v, ControlFlowNode entry, ControlFlowNode callsite, ControlFlowNode defn) {
    exists(Scope callee |
        non_module_scope_defines_or_uses_global(callee, v) and
        final_scope_executes(_, callee, callsite) and
        entry = callee.getEntryNode()
    ) and
    final_global_ssa_defn(v, defn, _) and
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

private predicate final_global_builtin_definition(GlobalVariable v, ControlFlowNode entry, Object value, ClassObject cls) {
    exists(Module m |
        v.getScope() = m and m.getEntryNode() = entry and
        value = builtin_object(v.getId()) and
        py_cobjecttypes(value, cls)
    )
}

private predicate final_global_defn_in_class(GlobalVariable v, ControlFlowNode defn, Class scope) {
    exists(ClassExpr cls |
        cls.getAFlowNode() = defn  and
        scope = cls.getInnerScope() |
        final_scope_defines_global(v, scope)
    )
}

/** DO NOT USE -- Internal, for testing. 
 * Whether `node` is the location of a global-SSA definition of `v`. `kind` describes the sort of definition for testing purposes.
 */
predicate final_global_ssa_defn(GlobalVariable v, ControlFlowNode node, string kind) {
    final_global_builtin_definition(v, node, _, _) and kind = "builtin"
    or
    final_global_phi_definition(v, node) and kind = "phi"
    or
    node.(NameNode).defines(v) and kind = "assignment"
    or
    node.(NameNode).deletes(v) and kind = "deletion"
    or
    final_global_callsite_defines_variable(v, node, _) and kind = "callsite"
    or
    final_global_prev_scope(v, node, _) and kind = "previous scope"
    or
    final_global_defn_from_callsite(v, node, _, _) and kind = "caller scope"
    or
    final_global_defn_in_class(v, node, _) and kind = "in class"
}

/** 
 * Whether the function `callee`, called from `callsite`, defines the global variable `v`
 */
private predicate final_global_callsite_defines_variable(GlobalVariable v, CallNode callsite, Function callee) {
    final_scope_defines_global(v, callee) and
    v.getScope() = callsite.getEnclosingModule() and
    exists(PyFunctionObject fo |
        callee = fo.getFunction() and
        callsite = penultimate_get_a_call(fo)
    )
}

pragma[noopt]
private ControlFlowNode final_get_global_ssa_defn_candidate(GlobalVariable v, NameNode use) {
    use.uses(v) and final_global_ssa_defn(v, result, _) and
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
ControlFlowNode final_get_global_ssa_defn(GlobalVariable v, NameNode use) {
    use.uses(v) and
    result = final_get_global_ssa_defn_candidate(v, use) and
    not exists(ControlFlowNode better |
        better = final_get_global_ssa_defn_candidate(v, use) and
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
ControlFlowNode final_get_global_ssa_defn_at_scope_end_candidate(GlobalVariable v, Scope f) {
    final_global_ssa_defn(v, result, _) and
    scope_exit(result, _, f)
}

/** Do not use -- testing only.
 * Get the best (closest) definition of `v` reaching the end of scope `f`
 */
pragma[nomagic]
ControlFlowNode final_get_global_ssa_defn_at_scope_end(GlobalVariable v, Scope f) {
    result = final_get_global_ssa_defn_at_scope_end_candidate(v, f) and
    not exists(ControlFlowNode better |
        better = penultimate_get_global_ssa_defn_at_scope_end_candidate(v, f) and
        result.strictlyDominates(better)
    )
}

/** Get the best (closest dominating) definition of `v` for callsite `call` (and callee entry point `entry`) */
private 
ControlFlowNode final_get_best_defn_for_callsite(GlobalVariable v, ControlFlowNode call, ControlFlowNode entry) {
    final_global_defn_from_callsite(v, entry, call, result) and
    not exists(ControlFlowNode better |
        final_global_defn_from_callsite(v, entry, call, better) and
        result.strictlyDominates(better)
    )
}

/** Whether the global SSA variable `(v, defn)` points-to `(value, cls, origin)` where `defn` is the entry point of a function. */ 
private 
predicate final_global_callee_ssa_points_to(GlobalVariable v, ControlFlowNode defn, Object value, ClassObject cls, ControlFlowNode origin) {
    exists(ControlFlowNode call, ControlFlowNode outer_defn |
        outer_defn = final_get_best_defn_for_callsite(v, call, defn) and
        final_global_ssa_points_to(v, outer_defn, value, cls, origin, _)
    )
}

/** Do not use -- testing only.
 * Whether the global SSA variable `(v, defn)` points-to `(value, cls, origin)`. The `kind` string is for testing.
 */
pragma [nomagic]
predicate final_global_ssa_points_to(GlobalVariable v, ControlFlowNode defn, Object value, ClassObject cls, ControlFlowNode origin, string kind) {
    final_global_builtin_definition(v, defn, value, cls) and origin = defn and kind = "builtin"
    or
    exists(Function f, ControlFlowNode d |
        final_global_callsite_defines_variable(v, defn, f) and
        d = final_get_global_ssa_defn_at_scope_end(v, f) and
        final_global_ssa_points_to(v, d, value, cls, origin, _)
    ) and kind = "callsite"
    or
    defn.(NameNode).defines(v) and final_points_to(defn, value, cls, origin) and kind = "assignment"
    or
    final_global_ssa_phi_points_to(v, defn, value, cls, origin) and kind = "phi"
    or
    exists(Scope pre, ControlFlowNode def |
        final_global_prev_scope(v, defn, pre) and
        def = final_get_global_ssa_defn_at_scope_end(v, pre) and
        final_global_ssa_points_to(v, def, value, cls, origin, _)
    ) and kind = "previous scope"
    or
    final_global_callee_ssa_points_to(v, defn, value, cls, origin) and kind = "caller scope"
    or
    exists(Class inner, ControlFlowNode d |
        final_global_defn_in_class(v, defn, inner) and
        d = final_get_global_ssa_defn_at_scope_end(v, inner) and
        final_global_ssa_points_to(v, d, value, cls, origin, _)
    ) and kind = "in class"
}

/** What the the SSA variable 'var' may point to, provided that it is a phi node, taking care to account 
 * for guards on the incoming edges. The points-to relation for an SSA phi-node is the union of its incoming 
 * SSA variables, excepting those values and classes that are explicitly guarded against.
 */
predicate final_global_ssa_phi_points_to(GlobalVariable v, BasicBlock phi, Object value, ClassObject cls, ControlFlowNode origin) {
    final_global_phi_definition(v, phi) and
    exists(ControlFlowNode incoming_defn, BasicBlock pred |
        incoming_defn = final_get_phi_argument_for_predecessor_block(v, phi, pred) |
        not final_global_prohibited_on_edge(v, incoming_defn, pred, phi, value, cls) and
        not final_global_must_have_boolean_value_on_edge(v, incoming_defn, pred, phi, value.booleanValue().booleanNot()) and
        final_global_ssa_points_to(v, incoming_defn, value, cls, origin, _)
    )
}
/** INTERNAL -- Do not not use */
pragma [inline]
predicate final_global_prohibited_on_edge(ControlledVariable var, ControlFlowNode defn, BasicBlock pred, BasicBlock succ, Object value, ClassObject cls) {
    exists(PenultimatePointsToFilter cond |
        defn = final_get_global_ssa_defn(var, cond.getRelevantUse(var))
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
predicate final_global_must_have_boolean_value_on_edge(GlobalVariable var, ControlFlowNode defn, BasicBlock pred, BasicBlock succ, boolean tf) {
    exists(IsTrue ist |
        ist.controlsEdge(var.(ControlledVariable), pred, succ, tf) and
        defn = final_get_global_ssa_defn(var, ist)
    )
}

pragma[nomagic]
private predicate defn_for_phi(ControlFlowNode defn, ControlFlowNode phi, GlobalVariable v) {
    final_global_phi_definition(v, phi) and
    final_global_ssa_defn(v, defn, _)
}

pragma [noopt]
private ControlFlowNode final_dominating_defn_for_phi_predecessor_block(GlobalVariable v, BasicBlock phi, BasicBlock pred) {
    defn_for_phi(result, phi, v) and
    exists(BasicBlock bb | 
        result.getBasicBlock() = bb 
        and 
        bb.dominates(pred)
    ) and
    pred = phi.getAPredecessor()
}

/** DO NOT USE -- For testing only */
ControlFlowNode final_get_phi_argument_for_predecessor_block(GlobalVariable v, BasicBlock phi, BasicBlock pred) {
    result = final_dominating_defn_for_phi_predecessor_block(v, phi, pred) and
    not exists(ControlFlowNode better |
        better = final_dominating_defn_for_phi_predecessor_block(v, phi, pred) and
        result.strictlyDominates(better)
    )
}

/** Get an object pointed to by a use (of a global variable) */
predicate final_global_use_points_to(NameNode use, Object value, ClassObject cls, ControlFlowNode origin) {
    exists(GlobalVariable v, ControlFlowNode defn, ControlFlowNode ssa_origin |
        defn = final_get_global_ssa_defn(v, use) and
        final_global_ssa_points_to(v, defn, value, cls, ssa_origin, _) 
        |
        if exists(Module m | ssa_origin = m.getEntryNode()) then
            origin = use
        else
            origin = ssa_origin
    )
    or
    use.isGlobal() and not exists(final_get_global_ssa_defn(_, use)) and
    value = builtin_object(use.getId()) and py_cobjecttypes(value, cls) and
    origin = use
}
