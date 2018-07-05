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

/**
 * Part of the combined points-to, call-graph and type-inference library.
 * The main relation `points_to(node, context, object, cls, origin)` relates a control flow node
 * to the possible objects it points-to the inferred types of those objects and the 'origin'
 * of those objects. The 'origin' is the point in source code that the object can be traced
 * back to.
 *
 * The predicates provided are not intended to be used directly (although they are available to the advanced user), but are exposed in the user API as methods on key classes.
 *
 * For example, the most important predicate in the points-to relation is:
 * ```ql
 * predicate FinalPointsTo::points_to(ControlFlowNode f, FinalContext ctx, Object value, ClassObject cls, ControlFlowNode origin)
 * ```
 * Where `f` is the control flow node representing something that might hold a value. `ctx` is the context in which `f` "points-to" `value` and may be "general" or from a specific call-site.
 * `value` is a static approximation to a value, such as a number, a class, or an object instantiation.
 * `cls` is the class of this value if known, or `theUnknownType()` which is an internal `ClassObject` and should not be exposed to the general QL user.
 * `origin` is the point in the source from where `value` originates and is useful when presenting query results.
 *
 * The `FinalPointsTo::points_to` relation is exposed at the user API level as
 * ```ql
 * ControlFlowNode.refersTo(Context context, Object value, ClassObject cls, ControlFlowNode origin)
 * ```
 *
 */

import python
private import PointsToContext
private import Base
private import semmle.python.types.Extensions
private import Layer0
private import Filters as BaseFilters
import semmle.dataflow.SSA

/** Get a `ControlFlowNode` from an object or `here`.
 * If the object is a ControlFlowNode then use that, otherwise fall back on `here`
 */
pragma[inline]
private ControlFlowNode origin_from_object_or_here(ObjectOrCfg object, ControlFlowNode here) {
    result = object
    or
    not object instanceof ControlFlowNode and result = here
}

module PenultimatePointsTo {

    
    module API {

        /** INTERNAL -- Use `FunctionObject.getACall()`.
         *
         * Gets a call to `func` with the given context. */
        
        CallNode get_a_call(FunctionObject func, PenultimateContext context) {
            function_call(func, context, result)
            or
            method_call(func, context, result)
        }

        /** INTERNAL -- Use `FunctionObject.getAFunctionCall()`.
         *
         * Holds if `call` is a function call to `func` with the given context. */
        
        predicate function_call(FunctionObject func, PenultimateContext context, CallNode call) {
            points_to(call.getFunction(), context, func, _, _)
        }

        /** INTERNAL -- Use `FunctionObject.getAMethodCall()`.
         *
         * Holds if `call` is a method call to `func` with the given context.  */
        
        predicate method_call(FunctionObject func, PenultimateContext context, CallNode call) {
            Calls::plain_method_call(func, context, call)
            or
            Calls::super_method_call(context, call, _, func)
        }

        /** INTERNAL -- Use `f.refersTo(value, cls, origin)` instead. */
        
        predicate points_to(ControlFlowNode f, PenultimateContext context, Object value, ClassObject cls, ControlFlowNode origin) {
            points_to_candidate(f, context, value, cls, origin) and
            Layer::reachable(f, context)
        }

        /** Gets the value that `expr` evaluates to (when converted to a boolean) when `use` refers to `(val, cls, origin)`
         * and `expr` is a test (a branch) and contains `use`. */
        
        boolean test_evaluates_boolean(ControlFlowNode expr, ControlFlowNode use, PenultimateContext context, Object val, ClassObject cls, ControlFlowNode origin) {
            test_contains(expr, use) and
            result = Filters::evaluates_boolean(expr, use, context, val, cls, origin)
        }

        /** INTERNAL -- Do not use.
         *
         * Holds if `package.name` points to `(value, cls, origin)`, where `package` is a package object. */
        
        predicate package_attribute_points_to(PackageObject package, string name, Object value, ClassObject cls, ControlFlowNode origin) {
            py_module_attributes(package.getInitModule().getModule(), name, value, cls, origin)
            or
            not module_defines_name(package.getInitModule().getModule(), name) and
            value = package.submodule(name) and cls = theModuleType() and origin = value
        }

        /** INTERNAL -- `Use m.attributeRefersTo(name, obj, origin)` instead.
         *
         * Holds if `m.name` points to `(value, cls, origin)`, where `m` is a (source) module. */
        
        predicate py_module_attributes(Module m, string name, Object obj, ClassObject cls, ControlFlowNode origin) {
            exists(EssaVariable var, ControlFlowNode exit, ObjectOrCfg orig, PenultimateContext imp |
                exit =  m.getANormalExit() and var.getAUse() = exit and
                var.getSourceVariable().getName() = name and
                ssa_variable_points_to(var, imp, obj, cls, orig) and
                imp.isImport() and
                not obj = undefinedVariable() |
                origin = origin_from_object_or_here(orig, exit)
            )
            or
            not exists(EssaVariable var | var.getAUse() = m.getANormalExit() and var.getSourceVariable().getName() = name) and
            if version111plus() then (
                exists(EssaVariable var, PenultimateContext imp |
                    var.getAUse() = m.getANormalExit() and var.getSourceVariable().getName() = "*" |
                    SSA::ssa_variable_named_attribute_points_to(var, imp, name, obj, cls, origin) and
                    imp.isImport()
                )
            ) else (
                /* Backwards compatibility with older databases (dating from before Sept 2017)
                 * Penultimate can be removed 2018, once the dbscheme has been upgraded from e7f9ea.
                 */
                exists(ModuleObject imported, ObjectOrCfg maybe_origin, ImportStar im |
                    has_import_star(m, im, imported) and
                    Layer::module_attribute_points_to(imported, name, obj, cls, maybe_origin) |
                    origin = origin_from_object_or_here(maybe_origin, im.getAFlowNode())
                )
            )
        }

        /** INTERNAL -- Use `ModuleObject.hasAttribute(name)`
         *
         *  Whether the module defines name. */
        
        predicate module_defines_name(Module mod, string name) {
            (
                exists(SsaVariable var | name = var.getId() and var.getAUse() = mod.getANormalExit())
                or
                import_star_defines_name(mod, name)
            )
        }

        /** INTERNAL -- Use `Version.isTrue()` instead.
         *
         * Holds if `cmp` points to a test on version that is `value`.
         * For example, if `cmp` is `sys.version[0] < "3"` then for, Python 2, `value` would be `true`. */
        
        predicate version_const(CompareNode cmp, PenultimateContext context, boolean value) {
            exists(ControlFlowNode fv, ControlFlowNode fc, Object val |
                comparison(cmp, fv, fc, _) and
                points_to(cmp, context, val, _, _) and
                value = val.booleanValue()
                |
                sys_version_info_slice(fv, context, _)
                or
                sys_version_info_index(fv, context, _, _)
                or
                sys_version_string_char0(fv, context, _, _)
                or
                points_to(fv, context, theSysHexVersionNumber(), _, _)
            )
            or
            value = version_tuple_compare(cmp, context).booleanValue()
        }

        /** Holds if `name` is defined in the module `m` by an `import *` statement within that module. */
        
        predicate import_star_defines_name(Module m, string name) {
            exists(ModuleObject imported_module, ImportStar import_stmt |
                has_import_star(m, import_stmt, imported_module)
                |
                module_exports(imported_module, name)
                or
                builtin_module_attribute(imported_module, name, _, _)
            )
        }

        /** INTERNAL -- Use `FunctionObject.getArgumentForCall(call, position)` instead.  */
        
        ControlFlowNode get_positional_argument_for_call(FunctionObject func, PenultimateContext context, CallNode call, int position) {
            result = Calls::get_argument_for_call_by_position(func, context, call, position)
            or
            exists(string name |
                result = Calls::get_argument_for_call_by_name(func, context, call, name) and
                func.getFunction().getArg(position).asName().getId() = name
            )
        }

        /** INTERNAL -- Use `FunctionObject.getNamedArgumentForCall(call, name)` instead.  */
        
        ControlFlowNode get_named_argument_for_call(FunctionObject func, PenultimateContext context, CallNode call, string name) {
          (
            result = Calls::get_argument_for_call_by_name(func, context, call, name)
            or
            exists(int position |
                result = Calls::get_argument_for_call_by_position(func, context, call, position) and
                func.getFunction().getArg(position).asName().getId() = name
            )
          )
        }

        /**  INTERNAL -- Public for testing only.
         *
         * Holds if `call` is a call to super() with for an object of class `self_type`
         * and the `start` class in the MRO. For example, for a call `super(T, self)`,
         * `self_type` is `type(self)` and `start` is `T`.
         *
         * Handles both Python 2 style `super(T, self)` and Python 3 style `super()`.
         */
        
        predicate super_call(CallNode call, PenultimateContext context, EssaVariable self, ClassObject start) {
            Layer0PointsTo::points_to(call.getFunction(), _, theSuperType(), _, _) and
            (
                points_to(call.getArg(0), context, start, _, _) and
                self.getASourceUse() = call.getArg(1)
                or
                major_version() = 3 and
                not exists(call.getArg(0)) and
                exists(Function func |
                    call.getScope() = func and
                    context.appliesToScope(func) and
                    /* Implicit class argument is lexically enclosing scope */
                    func.getScope() = start.getPyClass() and
                    /* Implicit 'self' is the 0th parameter */
                    self.getDefinition().(ParameterDefinition).getDefiningNode() = func.getArg(0).asName().getAFlowNode()
                )
            )
        }

        /** INTERNAL -- Use `FunctionObject.neverReturns()` instead.
         *  Whether function `func` never returns. Slightly conservative approximation, this predicate may be false
         * for a function that can never return. */
        
        predicate function_never_returns(FunctionObject func) {
            /* A Python function never returns if it has no normal exits that are not dominated by a
             * call to a function which itself never returns.
             */
            function_can_never_return(func)
            or
            exists(Function f |
                f = func.getFunction()
                |
                forall(BasicBlock exit |
                    exit = f.getANormalExit().getBasicBlock() |
                    exists(FunctionObject callee, BasicBlock call  |
                        get_a_call(callee, _).getBasicBlock() = call and
                        function_never_returns(callee) and
                        call.dominates(exit)
                    )
                )
            )
        }

        private predicate py_module_exports(ModuleObject mod, string name) {
            exists(Module m |
                m = mod.getModule() |
                m.declaredInAll(_) and m.declaredInAll(name)
                or
                not m.declaredInAll(_) and module_defines_name(m, name) and name.charAt(0) != "_"
            )
        }

        private predicate package_exports(PackageObject pack, string name) {
            not pack.getInitModule().getModule().declaredInAll(_) and name.charAt(0) != "_" and
            exists(ModuleObject sub |
                sub = pack.submodule(name) |
                explicitly_imported(sub)
            )
            or
            py_module_exports(pack.getInitModule(), name)
        }

        /** INTERNAL -- Use `m.exports(name)` instead. */
        
        predicate module_exports(ModuleObject mod, string name) {
            package_exports(mod, name)
            or
            py_module_exports(mod, name)
            or
            py_cmembers_versioned(mod, name, _, major_version().toString()) and
            name.charAt(0) != "_"
        }

        /** INTERNAL -- Use `m.importedAs(name)` instead.
         *
         * Holds if `import name` will import the module `m`. */
        
        predicate module_imported_as(ModuleObject m, string name) {
            /* Normal imports */
            m.getName() = name
            or
            /* sys.modules['name'] = m */
            exists(ControlFlowNode sys_modules_flow, ControlFlowNode n, ControlFlowNode mod |
              /* Use previous points-to here to avoid slowing down the recursion too much */
              exists(SubscriptNode sub, Object sys_modules |
                  sub.getValue() = sys_modules_flow and
                  Layer0PointsTo::points_to(sys_modules_flow, _, sys_modules, _, _) and
                  builtin_module_attribute(theSysModuleObject(), "modules", sys_modules, _) and
                  sub.getIndex() = n and
                  n.getNode().(StrConst).getText() = name and
                  sub.(DefinitionNode).getValue() = mod and
                  Layer0PointsTo::points_to(mod, _, m, _, _)
              )
            )
        }

        /** Holds if `call` is of the form `getattr(arg, "name")`. */
        
        predicate getattr(CallNode call, ControlFlowNode arg, string name) {
            Layer0PointsTo::points_to(call.getFunction(), _, builtin_object("getattr"), _, _) and
            call.getArg(1).getNode().(StrConst).getText() = name and
            arg = call.getArg(0)
        }

        /** Holds if `f` is the instantiation of an object, `cls(...)`.  */
        
        predicate instantiation(CallNode f, PenultimateContext context, ClassObject cls) {
            points_to(f.getFunction(), context, cls, _, _) and
            not cls = theTypeType() and
            not Calls::callToClassMayNotReturnInstance(cls)
        }

        /** Holds if `var` refers to `(value, cls, origin)` given the context `context`. */
        
        predicate ssa_variable_points_to(EssaVariable var, PenultimateContext context, Object value, ClassObject cls, ObjectOrCfg origin) {
            SSA::ssa_definition_points_to(var.getDefinition(), context, value, cls, origin)
        }

         /** Holds if f is of the form `obj.meth` where `obj` refers to an instance of `super` and
          * `function` is the method `T.meth` that is bound.
          */
        
        predicate super_bound_method(AttrNode f, PenultimateContext context, EssaVariable self, Object function) {
             exists(CallNode super_call, ControlFlowNode super_use, ClassObject mro_type, ClassObject start_type, ClassObject self_type, string name |
                 super_call(super_call, context, self, mro_type) and
                 points_to(super_use, context, super_call, _, _) and
                 ssa_variable_points_to(self, context, _, self_type, _) and
                 start_type = Types::next_in_mro(self_type, mro_type) and
                 super_use = f.getObject(name) and
                 Types::class_lookup_in_mro(self_type, start_type, name, function)
             )
         }

    }

    /** Predicates in this layer need to visible to the next layer, but not otherwise */
    
    module Layer {

        /* Holds if ControlFlowNode `f` is reachable, given the context `context`. */
        predicate reachable(ControlFlowNode f, PenultimateContext context) {
            context.appliesTo(f) and
            forall(ConditionBlock guard |
                guard.controls(f.getBasicBlock(), _) |
                exists(Object value |
                    points_to(guard.getLastNode(), context, value, _, _)
                    |
                    guard.controls(f.getBasicBlock(), true) and not value.booleanValue() = false
                    or
                    guard.controls(f.getBasicBlock(), false) and not value.booleanValue() = true
                )
            )
        }

        /* Holds if the edge `pred` -> `succ` is reachable, given the context `context`.
         */
        predicate controlledReachableEdge(BasicBlock pred, BasicBlock succ, PenultimateContext context) {
            exists(ConditionBlock guard, Object value |
                points_to(guard.getLastNode(), context, value, _, _)
                |
                guard.controlsEdge(pred, succ, true) and not value.booleanValue() = false
                or
                guard.controlsEdge(pred, succ, false) and not value.booleanValue() = true
            )
        }

        /** Holds if `mod.name` points to `(value, cls, origin)`, where `mod` is a module object. */
        predicate module_attribute_points_to(ModuleObject mod, string name, Object value, ClassObject cls, ObjectOrCfg origin) {
            py_module_attributes(mod.getModule(), name, value, cls, origin)
            or
            package_attribute_points_to(mod, name, value, cls, origin)
            or
            builtin_module_attribute(mod, name, value, cls) and origin = value
        }

        ClassObject class_get_meta_class_candidate(ClassObject cls) {
            result = class_explicit_metaclass(cls)
            or
            /* No declared or inherited metaclass */
            not has_explicit_metaclass(cls) and not cls.hasABase()
            and
            ( if baseless_is_new_style(cls) then
                  result = theTypeType()
              else
                  result = theClassType()
            )
            or
            result = class_get_meta_class_candidate(Types::class_base_type(cls, _))
        }

        predicate has_explicit_metaclass(ClassObject cls) {
            exists(EssaVariable var | var.getName() = "__metaclass__" and var.getAUse() = cls.getPyClass().getANormalExit())
            or
            exists(cls.declaredMetaClass())
            or
            exists(ClassObject cmeta | py_cobjecttypes(cls, cmeta) and is_c_metaclass(cmeta))
            or
            Layer0PointsTo::Types::six_add_metaclass(_, cls, _)
        }

        ClassObject class_explicit_metaclass(ClassObject cls) {
            exists(EssaVariable var |
                var.getName() = "__metaclass__" and var.getAUse() = cls.getPyClass().getANormalExit() and
                ssa_variable_points_to(var, _, result, _, _)
            )
            or
            points_to(cls.declaredMetaClass(), _, result, _, _)
            or
            py_cobjecttypes(cls, result) and is_c_metaclass(result)
            or
            exists(ControlFlowNode meta |
                Types::six_add_metaclass(_, cls, meta) and
                points_to(meta, _, result, _, _)
            )
        }

    }

    import API

    /* Holds if `f` points to a test on the OS that is `value`.
     * For example, if `f` is `sys.platform == "win32"` then, for Windows, `value` would be `true`.
     */
    private predicate os_const(ControlFlowNode f, PenultimateContext context, boolean value) {
        exists(string os |
            os_test(f, os, context) |
            value = true and py_flags_versioned("sys.platform", os, major_version().toString())
            or
            value = false and not py_flags_versioned("sys.platform", os, major_version().toString())
        )
    }

    /** Points-to before pruning. */
    pragma [nomagic]
    private predicate points_to_candidate(ControlFlowNode f, PenultimateContext context, Object value, ClassObject cls, ControlFlowNode origin) {
        simple_points_to(f, value, cls, origin) and context.appliesToScope(f.getScope())
        or
        f.isClass() and value = f  and origin = f and context.appliesToScope(f.getScope()) and
        (
            cls = Types::class_get_meta_class(value)
            or
            not exists(Layer0PointsTo::Layer::class_get_meta_class_candidate(value)) and cls = theTypeType()
        )
        or
        exists(boolean b |
            os_const(f, context, b)
            |
            value = theTrueObject() and b = true
            or
            value = theFalseObject() and b = false
        ) and cls = theBoolType() and origin = f
        or
        import_points_to(f, value, origin) and cls = theModuleType() and context.appliesToScope(f.getScope())
        or
        attribute_load_points_to(f, context, value, cls, origin)
        or
        getattr_points_to(f, context, value, cls, origin)
        or
        if_exp_points_to(f, context, value, cls, origin)
        or
        from_import_points_to(f, context, value, cls, origin)
        or
        use_points_to(f, context, value, cls, origin)
        or
        def_points_to(f, context, value, cls, origin)
        or
        Calls::call_points_to(f, context, value, cls, origin)
        or
        super_bound_method(f, context, _, _) and value = f and origin = f and cls = theBoundMethodType()
        or
        subscript_points_to(f, context, value, cls, origin)
        or
        sys_version_info_slice(f, context, cls) and value = theSysVersionInfoTuple() and origin = f
        or
        sys_version_info_index(f, context, value, cls) and origin = f
        or
        sys_version_string_char0(f, context, value, cls) and origin = f
        or
        six_metaclass_points_to(f, context, value, cls, origin)
        or
        binary_expr_points_to(f, context, value, cls, origin)
        or
        compare_expr_points_to(f, context, value, cls, origin)
        or
        not_points_to(f, context, value, cls, origin)
        or
    f.(PenultimateCustomPointsToFact).pointsTo(context, value, cls, origin)
    }

    /** The ESSA variable with fast-local lookup (LOAD_FAST bytecode). */
    private EssaVariable fast_local_variable(NameNode n) {
        n.isLoad() and
        result.getASourceUse() = n and
        result.getSourceVariable() instanceof FastLocalVariable
    }

    /** The ESSA variable with name-local lookup (LOAD_NAME bytecode). */
    private EssaVariable name_local_variable(NameNode n) {
        n.isLoad() and
        result.getASourceUse() = n and
        result.getSourceVariable() instanceof NameLocalVariable
    }

    /** The ESSA variable for the global variable lookup. */
    private EssaVariable global_variable(NameNode n) {
        n.isLoad() and
        result.getASourceUse() = n and
        result.getSourceVariable() instanceof GlobalVariable
    }

    private predicate use_points_to_maybe_origin(NameNode f, PenultimateContext context, Object value, ClassObject cls, ObjectOrCfg origin_or_obj) {
        ssa_variable_points_to(fast_local_variable(f), context, value, cls, origin_or_obj)
        or
        name_lookup_points_to_maybe_origin(f, context, value, cls, origin_or_obj)
        or
        not exists(fast_local_variable(f)) and not exists(name_local_variable(f)) and
        global_lookup_points_to_maybe_origin(f, context, value, cls, origin_or_obj)
    }

    pragma [noinline]
    private predicate local_variable_undefined(NameNode f, PenultimateContext context) {
        ssa_variable_points_to(name_local_variable(f), context, undefinedVariable(), _, _)
    }

    private predicate name_lookup_points_to_maybe_origin(NameNode f, PenultimateContext context, Object value, ClassObject cls, ObjectOrCfg origin_or_obj) {
        exists(EssaVariable var | var = name_local_variable(f) |
            ssa_variable_points_to(var, context, value, cls, origin_or_obj)
        )
        or
        local_variable_undefined(f, context) and
        global_lookup_points_to_maybe_origin(f, context, value, cls, origin_or_obj)
    }

    private predicate global_lookup_points_to_maybe_origin(NameNode f, PenultimateContext context, Object value, ClassObject cls, ObjectOrCfg origin_or_obj) {
        ssa_variable_points_to(global_variable(f), context, value, cls, origin_or_obj)
        or
        ssa_variable_points_to(global_variable(f), context, undefinedVariable(), _, _) and
        potential_builtin_points_to(f, value, cls, origin_or_obj)
        or
        not exists(global_variable(f)) and context.appliesToScope(f.getScope()) and
        potential_builtin_points_to(f, value, cls, origin_or_obj)
    }

    /** Gets an object pointed to by a use (of a variable). */
    private predicate use_points_to(NameNode f, PenultimateContext context, Object value, ClassObject cls, ControlFlowNode origin) {
        exists(ObjectOrCfg origin_or_obj |
            not value = undefinedVariable() and
            use_points_to_maybe_origin(f, context, value, cls, origin_or_obj) |
            origin = origin_from_object_or_here(origin_or_obj, f)
        )
    }

    /** Gets an object pointed to by the definition of an ESSA variable. */
    private predicate def_points_to(DefinitionNode f, PenultimateContext context, Object value, ClassObject cls, ControlFlowNode origin) {
        points_to(f.getValue(), context, value, cls, origin)
    }

    /** Holds if `f` points to `@six.add_metaclass(cls)\nclass ...`. */
    private predicate six_metaclass_points_to(ControlFlowNode f, PenultimateContext context, Object value, ClassObject cls, ControlFlowNode origin) {
        exists(ControlFlowNode meta |
            Types::six_add_metaclass(f, value, meta) and
            points_to(meta, context, cls, _, _)
        ) and
        origin = value
    }

    /** Holds if `obj.name` points to `(value, cls, orig)`. */
    pragma [noinline]
    private predicate class_or_module_attribute(Object obj, string name, Object value, ClassObject cls, ObjectOrCfg orig) {
        /* Normal class attributes */
        Types::class_attribute_lookup(obj, name, value, cls, orig) and not cls = theStaticMethodType()
        or
        /* Static methods of the class */
        exists(CallNode sm | Types::class_attribute_lookup(obj, name, sm, theStaticMethodType(), _) and sm.getArg(0) = value and cls = thePyFunctionType() and orig = value)
        or
        /* Module attributes */
        Layer::module_attribute_points_to(obj, name, value, cls, orig)
    }

    /** Holds if `f` points to `(value, cls, origin)` where `f` is an instance attribute, `x.attr`. */
    pragma [noinline]
    private predicate instance_attribute_load_points_to(AttrNode f, PenultimateContext context, Object value, ClassObject cls, ControlFlowNode origin) {
        f.isLoad() and
        exists(string name |
           named_attribute_points_to(f.getObject(name), context, name, value, cls, origin)
           or
           /* Static methods on the class of the instance */
           exists(CallNode sm, ClassObject icls |
              points_to(f.getObject(name), context, _, icls, _) and
              Types::class_attribute_lookup(icls, name, sm, theStaticMethodType(), _) and sm.getArg(0) = value and cls = thePyFunctionType() and origin = value
          )
       )
    }

    /** Holds if `f` points to `(value, cls, origin)` where `f` is a module or class attribute, `clazz.attr` or `mod.attr`. */
    pragma [noopt]
    private predicate class_or_module_attribute_node(AttrNode f, PenultimateContext context, Object value, ClassObject cls, ObjectOrCfg orig) {
        exists(string name, ControlFlowNode fval|
            f.isLoad() and fval = f.getObject(name) |
            exists(Object obj |
                points_to(fval, context, obj, _, _) and
                class_or_module_attribute(obj, name, value, cls, orig)
            )
        )
    }

    /** Holds if `f` is an attribute `x.attr` and points to `(value, cls, origin)`. */
    private predicate attribute_load_points_to(AttrNode f, PenultimateContext context, Object value, ClassObject cls, ControlFlowNode origin) {
        instance_attribute_load_points_to(f, context, value, cls, origin)
        or
        exists(ObjectOrCfg orig |
            class_or_module_attribute_node(f, context, value, cls, orig) and
            origin = origin_from_object_or_here(orig, f)
        )
        or
        points_to(f.getObject(), context, unknownValue(), theUnknownType(), origin) and value = unknownValue() and cls = theUnknownType()
    }

    /** Holds if `f` is an expression node `tval if cond else fval` and points to `(value, cls, origin)`. */
    private predicate if_exp_points_to(IfExprNode f, PenultimateContext context, Object value, ClassObject cls, ControlFlowNode origin) {
        points_to(f.getAnOperand(), context, value, cls, origin)
    }

    /** Holds if `f` is an import expression, `import mod` and points to `(value, cls, origin)`. */
    private predicate import_points_to(ControlFlowNode f, ModuleObject value, ControlFlowNode origin) {
        exists(string name, ImportExpr i |
            i.getAFlowNode() = f and i.getImportedModuleName() = name and
            module_imported_as(value, name) and
            origin = f
        )
    }

    /** Holds if `f` is a "from import" expression, `from mod import x` and points to `(value, cls, origin)`. */
    pragma [nomagic]
    private predicate from_import_points_to(ImportMemberNode f, PenultimateContext context, Object value, ClassObject cls, ControlFlowNode origin) {
        exists(EssaVariable var, ObjectOrCfg orig |
            live_import_from_dot_in_init(f, var) and
            ssa_variable_points_to(var, context, value, cls, orig) and
            origin = origin_from_object_or_here(orig, f)
        )
        or
        not live_import_from_dot_in_init(f, _) and
        exists(string name, ModuleObject mod |
            points_to(f.getModule(name), context, mod, _, _) |
            exists(ObjectOrCfg orig |
                Layer::module_attribute_points_to(mod, name, value, cls, orig) and
                origin = origin_from_object_or_here(orig, f)
            )
        )
    }

    /** Holds if `f`  is of the form `getattr(x, "name")` and x.name points to `(value, cls, origin)`. */
    private predicate getattr_points_to(CallNode f, PenultimateContext context, Object value, ClassObject cls, ControlFlowNode origin) {
        exists(ControlFlowNode arg, string name |
            named_attribute_points_to(arg, context, name, value, cls, origin) and
            getattr(f, arg, name)
        )
    }

    /** Whether the module is explicitly imported somewhere. */
    private predicate explicitly_imported(ModuleObject mod) {
        exists(ImportExpr ie | module_imported_as(mod, ie.getAnImportedModuleName()))
        or
        exists(ImportMember im | module_imported_as(mod, im.getImportedModuleName()))
    }

    /** Holds if an import star exists in the module m that imports the module `imported_module`, such that the flow from the import reaches the module exit. */
    private predicate has_import_star(Module m, ImportStar im, ModuleObject imported_module) {
        exists(string name |
            module_imported_as(imported_module, name) and
            name = im.getImportedModuleName() and
            im.getScope() = m and
            im.getAFlowNode().getBasicBlock().reachesExit()
        )
    }

    /** Track bitwise expressions so we can handle integer flags and enums.
     * Tracking too many binary expressions is likely to kill performance.
     */
    private predicate binary_expr_points_to(BinaryExprNode b, PenultimateContext context, Object value, ClassObject cls, ControlFlowNode origin) {
        cls = theIntType() and
        exists(ControlFlowNode left, ControlFlowNode right |
            bitwise_expression_node(b, left, right) and
            points_to(left, context, _, cls, _) and
            points_to(right, context, _, cls, _)
        ) and
        value = origin and origin = b
    }

    pragma [noinline]
    private predicate incomparable_values(CompareNode cmp, PenultimateContext context) {
        exists(ControlFlowNode left, ControlFlowNode right |
            cmp.operands(left, _, right) and
            exists(Object lobj, Object robj |
                points_to(left, context, lobj, _, _) and
                points_to(right, context, robj, _, _) |
                not Filters::comparable_value(lobj)
                or
                not Filters::comparable_value(robj)
            )
        )
    }

    pragma [noinline]
    private Object in_tuple(CompareNode cmp, PenultimateContext context) {
        exists(ControlFlowNode left, ControlFlowNode right |
            cmp.operands(left, any(In i), right) and
            exists(Object lobj, TupleObject tuple |
                points_to(left, context, lobj, _, _) and
                points_to(right, context, tuple, _, _)
                |
                lobj = tuple.getBuiltinElement(_) and result = theTrueObject()
                or
                not lobj = tuple.getBuiltinElement(_) and result = theFalseObject()
            )
        )
    }

    pragma [noinline]
    private predicate const_compare(CompareNode cmp, PenultimateContext context, int comp, boolean strict) {
        exists(ControlFlowNode left, ControlFlowNode right |
            inequality(cmp, left, right, strict) and
            (
                exists(NumericObject n1, NumericObject n2 |
                    points_to(left, context, n1, _, _) and
                    points_to(right, context, n2, _, _) and
                    comp = int_compare(n1, n2)
                )
                or
                exists(StringObject s1, StringObject s2|
                    points_to(left, context, s1, _, _) and
                    points_to(right, context, s2, _, _) and
                    comp = string_compare(s1, s2)
                )
            )
        )
    }

    pragma [noinline]
    private Object version_tuple_compare(CompareNode cmp, PenultimateContext context) {
        exists(ControlFlowNode lesser, ControlFlowNode greater, boolean strict |
            inequality(cmp, lesser, greater, strict) and
            exists(TupleObject tuple, int comp |
                points_to(lesser, context, tuple, _, _) and
                points_to(greater, context, theSysVersionInfoTuple(), _, _) and
                comp = version_tuple_compare(tuple)
                or
                points_to(lesser, context, theSysVersionInfoTuple(), _, _) and
                points_to(greater, context, tuple, _, _) and
                comp = version_tuple_compare(tuple)*-1
                |
                comp = -1 and result = theTrueObject()
                or
                comp = 0 and strict = false and result = theTrueObject()
                or
                comp = 0 and strict = true and result = theFalseObject()
                or
                comp = 1 and result = theFalseObject()
            )
        )
    }
/*
    pragma [noinline]
    private Object version_hex_compare(CompareNode cmp, PenultimateContext context) {
        exists(ControlFlowNode lesser, ControlFlowNode greater, boolean strict |
            inequality(cmp, lesser, greater, strict) and
            exists(TupleObject tuple, int comp |
                points_to(lesser, context, tuple, _, _) and
                points_to(greater, context, theSysHexVersionNumber(), _, _) and
                comp = version_tuple_compare(tuple)
                or
                points_to(lesser, context, theSysHexVersionNumber(), _, _) and
                points_to(greater, context, tuple, _, _) and
                comp = version_hex_compare(tuple)*-1
                |
                comp = -1 and result = theTrueObject()
                or
                comp = 0 and strict = false and result = theTrueObject()
                or
                comp = 0 and strict = true and result = theFalseObject()
                or
                comp = 1 and result = theFalseObject()
            )
        )
    }
*/
    private predicate compare_expr_points_to(CompareNode cmp, PenultimateContext context, Object value, ClassObject cls, ControlFlowNode origin) {
        equality_expr_points_to(cmp, context, value, cls, origin)
        or
        cls = theBoolType() and origin = cmp and
        (
            incomparable_values(cmp, context) and
            (value = theFalseObject() or value = theTrueObject())
            or
            value = in_tuple(cmp, context)
            or
            exists(int comp, boolean strict |
                const_compare(cmp, context, comp, strict)
                |
                comp = -1 and value = theTrueObject()
                or
                comp = 0 and strict = false and value = theTrueObject()
                or
                comp = 0 and strict = true and value = theFalseObject()
                or
                comp = 1 and value = theFalseObject()
            )
            or
            value = version_tuple_compare(cmp, context)
        )
    }

    pragma[inline]
    private int int_compare(NumericObject n1, NumericObject n2) {
        exists(int i1, int i2 |
            i1 = n1.intValue() and i2 = n2.intValue() |
            i1 = i2 and result = 0
            or
            i1 < i2 and result = -1
            or
            i1 > i2 and result = 1
        )
    }

    pragma[inline]
    private int string_compare(StringObject s1, StringObject s2) {
        exists(string a, string b |
            a = s1.getText() and b = s2.getText() |
            a = b and result = 0
            or
            a < b and result = -1
            or
            a > b and result = 1
        )
    }

    private predicate not_points_to(UnaryExprNode f, PenultimateContext context, Object value, ClassObject cls, ControlFlowNode origin) {
        f.getNode().getOp() instanceof Not and
        cls = theBoolType() and origin = f and
        exists(Object operand |
            points_to(f.getOperand(), context, operand, _, _)
            |
            not operand.booleanValue() = true and value = theTrueObject()
            or
            not operand.booleanValue() = false and value = theFalseObject()
        )
    }

    private predicate equality_expr_points_to(CompareNode cmp, PenultimateContext context, Object value, ClassObject cls, ControlFlowNode origin) {
        cls = theBoolType() and origin = cmp and
        exists(ControlFlowNode x, ControlFlowNode y, Object xobj, Object yobj, boolean is |
            BaseFilters::equality_test(cmp, x, is, y) and
            points_to(x, context, xobj, _, _) and
            points_to(y, context, yobj, _, _) and
            Filters::equatable_value(xobj) and Filters::equatable_value(yobj)
            |
            xobj = yobj and is = true and value = theTrueObject()
            or
            xobj != yobj and is = true and value = theFalseObject()
            or
            xobj = yobj and is = false and value = theFalseObject()
            or
            xobj != yobj and is = false and value = theTrueObject()
        )
    }

    private predicate subscript_points_to(SubscriptNode sub, PenultimateContext context, Object value, ClassObject cls, ControlFlowNode origin) {
        exists(Object unknownCollection |
            varargs_points_to(unknownCollection, _) or
            kwargs_points_to(unknownCollection, _)
            |
            sub.isLoad() and
            points_to(sub.getValue(), context, unknownCollection, _, _) and
            value = unknownValue() and cls = theUnknownType() and origin = sub
        )
        or
        points_to(sub.getValue(), context, unknownValue(), _, _) and
        value = unknownValue() and cls = theUnknownType() and origin = sub
    }

    /* **************
     * VERSION INFO *
     ****************/

    /** Holds if `s` points to `sys.version_info[0]`. */
    private predicate sys_version_info_index(SubscriptNode s, PenultimateContext context, NumericObject value, ClassObject cls) {
        points_to(s.getValue(), context, theSysVersionInfoTuple(), _, _) and
        exists(NumericObject zero |
            zero.intValue() = 0 |
            points_to(s.getIndex(), context, zero, _, _)
        ) and
        value.intValue() = major_version() and
        cls = theIntType()
    }

    /** Holds if `s` points to `sys.version_info[:x]` or `sys.version_info[:]`. */
    private predicate sys_version_info_slice(SubscriptNode s, PenultimateContext context, ClassObject cls) {
        points_to(s.getValue(), context, theSysVersionInfoTuple(), cls, _) and
        exists(Slice index | index = s.getIndex().getNode() |
            not exists(index.getStart())
        )
    }

    /** Holds if `s` points to `sys.version[0]`. */
    private predicate sys_version_string_char0(SubscriptNode s, PenultimateContext context, Object value, ClassObject cls) {
        points_to(s.getValue(), context, theSysVersionString(), cls, _) and
        exists(NumericObject zero |
            zero.intValue() = 0 |
            points_to(s.getIndex(), context, zero, _, _)
        )
        and
        value = object_for_string(major_version().toString())
    }

    /* Version tests. Ignore micro and release parts. Treat major, minor as a single version major*10+minor
     * Currently cover versions 0.9 to 4.0
     */

    /** Helper for `version_const`. */
    private predicate comparison(CompareNode cmp, ControlFlowNode fv, ControlFlowNode fc, string opname) {
        exists(Cmpop op |
            cmp.operands(fv, op, fc) and opname = op.getSymbol()
            or
            cmp.operands(fc, op, fv) and opname = reversed(op)
        )
    }

    /** Helper for `version_const`. */
    private predicate inequality(CompareNode cmp, ControlFlowNode lesser, ControlFlowNode greater, boolean strict) {
        exists(Cmpop op |
            cmp.operands(lesser, op, greater) and op.getSymbol() = "<" and strict = true
            or
            cmp.operands(lesser, op, greater) and op.getSymbol() = "<=" and strict = false
            or
            cmp.operands(greater, op, lesser) and op.getSymbol() = ">" and strict = true
            or
            cmp.operands(greater, op, lesser) and op.getSymbol() = ">=" and strict = false
        )
    }

    /** Holds if `f` is a test for the O/S. */
    private predicate os_test(ControlFlowNode f, string os, PenultimateContext context) {
        exists(ControlFlowNode c |
             os_compare(c, os) and
             points_to(f, context, _, _, c)
        )
    }

    predicate named_attribute_points_to(ControlFlowNode f, PenultimateContext context, string name, Object value, ClassObject cls, ControlFlowNode origin) {
        exists(EssaVariable var |
            var.getAUse() = f |
            SSA::ssa_variable_named_attribute_points_to(var, context, name, value, cls, origin)
        )
        or
        exists(ClassObject c, EssaVariable self, Function init |
            instantiation(f, context, c) and
            init = c.getPyClass().getInitMethod() and
            self.getAUse() = init.getANormalExit() and
            SSA::ssa_variable_named_attribute_points_to(self, context, name, value, cls, origin)
        )
    }

    private module Calls {

         /** Holds if `f` is a call to type() with a single argument `arg` */
         private predicate call_to_type(CallNode f, ControlFlowNode arg, PenultimateContext context) {
             points_to(f.getFunction(), context, theTypeType(), _, _) and not exists(f.getArg(1)) and arg = f.getArg(0)
         }

         /** INTERNAL -- Do not not use.
          *
          * Whether a call to this class may not return an instance of this class.
          */
         predicate callToClassMayNotReturnInstance(ClassObject cls) {
             /* Django does this, so we need to account for it */
             exists(Function init, LocalVariable self |
                 /* `self.__class__ = ...` in the `__init__` method */
                 cls.getPyClass().getInitMethod() = init and
                 self.isSelf() and self.getScope() = init and
                 exists(AttrNode a | a.isStore() and a.getObject("__class__") = self.getAUse())
             )
             or
             /* Most builtin types "declare" __new__, such as `int`, yet are well behaved. */
             not cls.isBuiltin() and class_declares_attribute(cls, "__new__")
             or
             callToClassMayNotReturnInstance(Layer0PointsTo::Types::get_an_improper_super_type(cls))
         }

         pragma [noinline]
         predicate call_to_type_known_python_class_points_to(CallNode f, PenultimateContext context, Object value, ClassObject cls, ControlFlowNode origin) {
             exists(ControlFlowNode arg |
                 call_to_type(f, arg, context) and
                 points_to(arg, context, _, value, _)
             ) and
             origin.getNode() = value.getOrigin() and
             cls = theTypeType()
         }

         pragma [noinline]
         predicate call_to_type_known_builtin_class_points_to(CallNode f, PenultimateContext context, Object value, ClassObject cls, ControlFlowNode origin) {
             exists(ControlFlowNode arg |
                 call_to_type(f, arg, context) |
                 points_to(arg, context, _, value, _)
             ) and
             not exists(value.getOrigin()) and
             origin = f and cls = theTypeType()
         }

         pragma [noinline]
         predicate call_points_to_builtin_function(CallNode f, PenultimateContext context, Object value, ClassObject cls, ControlFlowNode origin) {
             exists(BuiltinCallable b |
                 not b = builtin_object("isinstance") and
                 not b = builtin_object("issubclass") and
                 f = get_a_call(b, context) and
                 cls = b.getAReturnType()
             ) and
             f = origin and
             if cls = theNoneType() then
                 value = theNoneObject()
             else
                 value = f
         }

         /** holds if `f` is a call to `isinstance` or `issubclass`. */
         predicate type_test_call(CallNode f, PenultimateContext context, Object value, ClassObject cls, ControlFlowNode origin) {
            cls = theBoolType() and origin = f and
            (
                call_to_isinstance(f, context, value)
                or
                call_to_issubclass(f, context, value)
            )
         }

         /** Holds if call is to an object that always returns its first argument.
          * Typically, this is for known decorators and the like.
          * The current implementation only accounts for instances of `zope.interface.declarations.implementer`.
          */
         private predicate annotation_call(CallNode f, PenultimateContext context, Object value, ClassObject cls, ControlFlowNode origin) {
            exists(ClassObject implementer |
                points_to(f.getArg(0), context, value, cls, origin) and
                points_to(f.getFunction(), context, _, implementer, _) |
                implementer.getName() = "implementer" and
                implementer.getPyClass().getEnclosingModule().getName() = "zope.interface.declarations"
            )
         }

         private predicate call_to_isinstance(CallNode f, PenultimateContext context, Object value) {
              exists(ControlFlowNode clsNode, ControlFlowNode objNode, ClassObject objcls |
                points_to(objNode, context, _, objcls, _) and
                BaseFilters::isinstance(f, clsNode, objNode) |
                exists(ClassObject scls |
                    points_to(clsNode, _, scls, _, _) |
                    scls = Layer0PointsTo::Types::get_an_improper_super_type(objcls) and value = theTrueObject()
                    or
                    not scls = Layer0PointsTo::Types::get_an_improper_super_type(objcls) and value = theFalseObject()
                )
                or exists(TupleObject t, ClassObject scls |
                    Layer0PointsTo::points_to(clsNode, _, t, _, _) and
                    (
                        scls = t.getBuiltinElement(_)
                        or
                        Layer0PointsTo::points_to(t.getSourceElement(_), _, scls, _, _)
                    )
                    |
                    scls = Layer0PointsTo::Types::get_an_improper_super_type(objcls) and value = theTrueObject()
                    or
                    not scls = Layer0PointsTo::Types::get_an_improper_super_type(objcls) and value = theFalseObject()
                )
                or
                objcls = theUnknownType() and (value = theTrueObject() or value = theFalseObject())
            )
         }

         private predicate call_to_issubclass(CallNode f, PenultimateContext context, Object value) {
             exists(ControlFlowNode clsNode, ControlFlowNode objNode, Object objcls |
                points_to(objNode, context, objcls, _, _) and
                BaseFilters::issubclass(f, clsNode, objNode) |
                exists(ClassObject scls |
                    points_to(clsNode, _, scls, _, _) |
                    scls = Layer0PointsTo::Types::get_an_improper_super_type(objcls) and value = theTrueObject()
                    or
                    not scls = Layer0PointsTo::Types::get_an_improper_super_type(objcls) and value = theFalseObject()
                )
                or
                (objcls = unknownValue() or objcls = theUnknownType()) and
                (value = theTrueObject() or value = theFalseObject())
            )
         }

         pragma [noinline]
         predicate call_to_procedure_points_to(CallNode f, PenultimateContext context, Object value, ClassObject cls, ControlFlowNode origin) {
             exists(PyFunctionObject func |
                 f = get_a_call(func, context) and
                 implicitly_returns(func, value, cls) and origin.getNode() = func.getOrigin()
             )
         }

         predicate call_to_unknown(CallNode f, PenultimateContext context, Object value, ClassObject cls, ControlFlowNode origin) {
              value = unknownValue() and cls = theUnknownType() and origin = f
              and
              exists(ControlFlowNode callable |
                  callable = f.getFunction() or
                  callable = f.getFunction().(AttrNode).getObject()
                  |
                  points_to(callable, context, unknownValue(), _, _)
              )
         }

         predicate call_to_generator_points_to(CallNode f, PenultimateContext context, Object value, ClassObject cls, ControlFlowNode origin) {
             exists(PyFunctionObject func |
                 f = get_a_call(func, context) |
                 func.getFunction().isGenerator() and origin = f and value = f and cls = theGeneratorType()
             )
         }

         /* Helper for call_points_to_python_function */
         predicate return_val_points_to(PyFunctionObject func, PenultimateContext context, Object value, ClassObject cls, ControlFlowNode origin) {
             exists(ControlFlowNode rval |
                 rval = func.getAReturnedNode() and
                 points_to(rval, context, value, cls, origin)
             )
         }

         pragma [noinline]
         predicate call_points_to_python_function(CallNode f, PenultimateContext context, Object value, ClassObject cls, ControlFlowNode origin) {
             exists(PyFunctionObject func, PenultimateContext callee |
                 return_val_points_to(func, callee, value, cls, origin) and
                 callee.fromCall(f, func, context)
             )
         }

         /** A call, including calls to `type(arg)`, functions and classes.
          *
          * Call analysis logic
          * ===================
          *  There are five possibilities (that we currently account for) here.
          * 1. `type(known_type)` where we know the class of `known_type` and we know its origin
          * 2. `type(known_type)` where we know the class of `known_type`,
          *        but we don't know its origin (because it is a builtin type)
          * 3. `Class(...)` where Class is any class except type (with one argument) and calls to that class return instances of that class
          * 4. `func(...)` where we know the return type of func (because it is a builtin function)
          * 5. `func(...)` where we know the returned object and origin of func (because it is a Python function)
          */
         predicate call_points_to(CallNode f, PenultimateContext context, Object value, ClassObject cls, ControlFlowNode origin) {
             /* Case 1 */
             call_to_type_known_python_class_points_to(f, context, value, cls, origin)
             or
             /* Case 2 */
             call_to_type_known_builtin_class_points_to(f, context, value, cls, origin)
             or
             /* Case 3 */
             instantiation(f, context, cls) and value = f and f = origin
             or
             /* Case 4 */
             call_points_to_builtin_function(f, context, value, cls, origin)
             or
             /* Case 5a */
             call_points_to_python_function(f, context, value, cls, origin)
             or
             /* Case 5b */
             call_to_generator_points_to(f, context, value, cls, origin)
             or
             /* Case 5c */
             call_to_procedure_points_to(f, context, value, cls, origin)
             or
             call_to_unknown(f, context, value, cls, origin)
             or
             type_test_call(f, context, value, cls, origin)
             or
             annotation_call(f, context, value, cls, origin)
         }

         /** INTERNAL -- Public for testing only.
          * Whether `call` is a call to `method` of the form `super(...).method(...)`
          */
         predicate super_method_call(PenultimateContext context, CallNode call, EssaVariable self, FunctionObject method) {
             exists(ControlFlowNode func, AttrNode bound_method |
                 call.getFunction() = func and
                 points_to(func, context, bound_method, _, _) and
                 super_bound_method(bound_method, context, self, method)
             )
         }

         /** INTERNAL -- Use `FunctionObject.getAMethodCall()`. */
         pragma [nomagic]
         predicate plain_method_call(FunctionObject func, PenultimateContext context, CallNode call) {
             exists(ControlFlowNode attr, ClassObject cls, string name |
                 attr = call.getFunction() and
                 receiver_type_for(cls, name, attr, context) and
                 Types::class_attribute_lookup(cls, name, func, _, _)
             )
         }

         /** INTERNAL -- Do not use; part of the internal API.
          *
          * Whether cls `cls` is the receiver type of an attribute access `n`.
          *  Also bind the name of the attribute.
          */
         predicate receiver_type_for(ClassObject cls, string name, ControlFlowNode n, PenultimateContext context) {
             /* `super().meth()` is not a method on `super` */
             cls != theSuperType() and
             exists(Object o |
                 /* list.__init__() is not a call to type.__init__() */
                 not o instanceof ClassObject |
                 points_to(n.(AttrNode).getObject(name), context, o, cls, _)
             )
             or
             exists(PlaceHolder p, Variable v |
                 n.getNode() = p and n.(NameNode).uses(v) and name = v.getId() and
                 p.getScope().getScope() = cls.getPyClass() and context.appliesTo(n)
             )
         }

         /** Gets the argument for the parameter at `position` where `call` is a call to `func`.
          * Handles method calls, such that for a call `x.foo()` with `position equal to 0, the result is `x`.
          */
         pragma [nomagic]
         ControlFlowNode get_argument_for_call_by_position(FunctionObject func, PenultimateContext context, CallNode call, int position) {
             method_call(func, context, call) and
             (
                 result = call.getArg(position-1)
                 or
                 position = 0 and result = call.getFunction().(AttrNode).getObject()
             )
             or
             function_call(func, context, call) and
             result = call.getArg(position)
         }

         /** Holds if `value` is the value attached to the keyword argument `name` in `call`. */
         predicate keyword_value_for_call(CallNode call, string name, ControlFlowNode value) {
             exists(Keyword kw |
                 call.getNode().getAKeyword() = kw |
                 kw.getArg() = name and kw.getValue() = value.getNode() and
                 value.getBasicBlock().dominates(call.getBasicBlock())
             )
         }

         /** Gets the value for the keyword argument `name` in `call`, where `call` calls `func` in context. */
         ControlFlowNode get_argument_for_call_by_name(FunctionObject func, PenultimateContext context, CallNode call, string name) {
             call = get_a_call(func, context) and
             keyword_value_for_call(call, name, result)
         }

         /** Holds if `func` implicitly returns the `None` object */
         predicate implicitly_returns(PyFunctionObject func, Object none_, ClassObject noneType) {
            noneType = theNoneType() and not func.getFunction().isGenerator() and none_ = theNoneObject() and
            (
              not exists(func.getAReturnedNode()) and exists(func.getFunction().getANormalExit())
              or
              exists(Return ret | ret.getScope() = func.getFunction() and not exists(ret.getValue()))
            )
         }

    }

    
    module Flow {

        /** Model the transfer of values at scope-entry points. Transfer from `(pred_var, pred_context)` to `(succ_def, succ_context)`. */
        
        predicate scope_entry_value_transfer(EssaVariable pred_var, PenultimateContext pred_context, ScopeEntryDefinition succ_def, PenultimateContext succ_context) {
            scope_entry_value_transfer_from_earlier(pred_var, pred_context, succ_def, succ_context)
            or
            callsite_entry_value_transfer(pred_var, pred_context, succ_def, succ_context)
            or
            pred_context.isImport() and pred_context = succ_context and
            class_entry_value_transfer(pred_var, succ_def)
        }

        /** Helper for `scope_entry_value_transfer`. Transfer of values from a temporally earlier scope to later scope.
         * Earlier and later scopes are, for example, a module and functions in that module, or an __init__ method and another method. */
        pragma [noinline]
        private predicate scope_entry_value_transfer_from_earlier(EssaVariable pred_var, PenultimateContext pred_context, ScopeEntryDefinition succ_def, PenultimateContext succ_context) {
            exists(Scope pred_scope, Scope succ_scope |
                BaseFlow::scope_entry_value_transfer_from_earlier(pred_var, pred_scope, succ_def, succ_scope) and
                succ_context.appliesToScope(succ_scope)
                |
                succ_context.isRuntime() and succ_context = pred_context
                or
                pred_context.isImport() and pred_scope instanceof ImportTimeScope and succ_context.fromRuntime()
                or
                /* If predecessor scope is main, then we assume that any global defined exactly once
                 * is available to all functions. Although not strictly true, this gives less surprising
                 * results in practice. */
                pred_context.isMain() and pred_scope instanceof Module and succ_context.fromRuntime() and
                not strictcount(pred_var.getSourceVariable().(Variable).getAStore()) > 1
            )
        }

        /** Helper for `scope_entry_value_transfer`.
         * Transfer of values from the callsite to the callee, for enclosing variables, but not arguments/parameters. */
        pragma [noinline]
        private predicate callsite_entry_value_transfer(EssaVariable caller_var, PenultimateContext caller_context, ScopeEntryDefinition entry_def, PenultimateContext callee_context) {
            exists(CallNode callsite, FunctionObject f, Variable var |
                scope_entry_function_and_variable(entry_def, f, var) and
                callee_context.fromCall(callsite, f, caller_context) and
                caller_var.getSourceVariable() = var and
                caller_var.getAUse() = callsite
            )
        }

        /** Helper for callsite_entry_value_transfer to improve join-order */
        private predicate scope_entry_function_and_variable(ScopeEntryDefinition entry_def, FunctionObject f, Variable var) {
            exists(Function func |
                func = f.getFunction() |
                entry_def.getDefiningNode() = func.getEntryNode() and
                not var.getScope() = func and
                entry_def.getSourceVariable() = var
            )
        }

        /** Helper for `scope_entry_value_transfer`. */
        private
        predicate class_entry_value_transfer(EssaVariable pred_var, ScopeEntryDefinition succ_def) {
            exists(ImportTimeScope scope, ControlFlowNode class_def |
                class_def = pred_var.getAUse() and
                scope.entryEdge(class_def, succ_def.getDefiningNode()) and
                pred_var.getSourceVariable() = succ_def.getSourceVariable()
            )
        }

        /**  Gets the ESSA variable from which `def` acquires its value, when a call occurs.
         * Helper for `callsite_points_to`. */
        
        predicate callsite_exit_value_transfer(EssaVariable callee_var, PenultimateContext callee_context, CallsiteRefinement def, PenultimateContext callsite_context) {
            exists(FunctionObject func, Variable var |
                callee_context.fromCall(def.getCall(), func, callsite_context) and
                def.getSourceVariable() = var and
                var_at_exit(var, func, callee_var)
            )
        }

        /* Helper for callsite_exit_value_transfer */
        private predicate var_at_exit(Variable var, FunctionObject func, EssaVariable evar) {
            not var instanceof LocalVariable and
            evar.getSourceVariable() = var and
            evar.getScope() = func.getFunction() and
            evar.reachesExit()
        }

        /** Holds if the `(argument, caller)` pair matches up with `(param, callee)` pair across call. */
        
        predicate callsite_argument_transfer(ControlFlowNode argument, PenultimateContext caller, ParameterDefinition param, PenultimateContext callee) {
            exists(CallNode call, PyFunctionObject func, int n, int offset |
                callsite_calls_function(call, caller, func, callee, offset) and
                argument = call.getArg(n) and
                param = func.getParameter(n+offset)
            )
        }

        
        predicate callsite_calls_function(CallNode call, PenultimateContext caller, PyFunctionObject func, PenultimateContext callee, int parameter_offset) {
            /* Functions */
            callee.fromCall(call, func, caller) and
            function_call(func, caller, call) and
            parameter_offset = 0
            or
            /* Methods */
            callee.fromCall(call, func, caller) and
            method_call(func, caller, call) and
            parameter_offset = 1
            or
            /* Classes */
            exists(ClassObject cls |
                instantiation(call, caller, cls) and
                Types::class_attribute_lookup(cls, "__init__", func, _, _) and
                parameter_offset = 1 and
                callee.fromCall(call, caller)
            )
        }

        /** Helper for `import_star_points_to`. */
        
        predicate module_and_name_for_import_star(ModuleObject mod, string name, ImportStarRefinement def, PenultimateContext context) {
            points_to(def.getDefiningNode().(ImportStarNode).getModule(), context, mod, _, _) and
            name = def.getSourceVariable().getName()
        }

        /** Holds if `def` is technically a definition of `var`, but the `from ... import *` does not in fact define `var`. */
        
        predicate variable_not_redefined_by_import_star(EssaVariable var, PenultimateContext context, ImportStarRefinement def) {
            var = def.getInput() and
            exists(ModuleObject mod |
                points_to(def.getDefiningNode().(ImportStarNode).getModule(), context, mod, _, _) and
                not module_exports(mod, var.getSourceVariable().getName())
            )
        }

    }

    private module SSA {


        /** Holds if the phi-function `phi` refers to `(value, cls, origin)` given the context `context`. */
        pragma [noinline]
        private predicate ssa_phi_points_to(PhiFunction phi, PenultimateContext context, Object value, ClassObject cls, ObjectOrCfg origin) {
            exists(EssaVariable input, BasicBlock pred |
                input = phi.getInput(pred) and
                ssa_variable_points_to(input, context, value, cls, origin)
                |
                Layer::controlledReachableEdge(pred, phi.getBasicBlock(), context)
                or
                not exists(ConditionBlock guard | guard.controlsEdge(pred, phi.getBasicBlock(), _))
            )
            or
            ssa_variable_points_to(phi.getShortCircuitInput(), context, value, cls, origin)
        }

        /** Holds if the ESSA definition `def`  refers to `(value, cls, origin)` given the context `context`. */
        predicate ssa_definition_points_to(EssaDefinition def, PenultimateContext context, Object value, ClassObject cls, ObjectOrCfg origin) {
            ssa_phi_points_to(def, context, value, cls, origin)
            or
            ssa_node_definition_points_to(def, context, value, cls, origin)
            or
            Filters::ssa_filter_definition_points_to(def, context, value, cls, origin)
            or
            ssa_node_refinement_points_to(def, context, value, cls, origin)
        }

        pragma [nomagic]
        private predicate ssa_node_definition_points_to_unpruned(EssaNodeDefinition def, PenultimateContext context, Object value, ClassObject cls, ObjectOrCfg origin) {
            assignment_points_to(def, context, value, cls, origin)
            or
            parameter_points_to(def, context, value, cls, origin)
            or
            self_parameter_points_to(def, context, value, cls, origin)
            or
            delete_points_to(def, context, value, cls, origin)
            or
            scope_entry_points_to(def, context, value, cls, origin)
            or
            implicit_submodule_points_to(def, context, value, cls, origin)
            or
            module_name_points_to(def, context, value, cls, origin)
            /*
             * No points-to for non-local function entry definitions yet.
             */
        }

        pragma [noinline]
        private predicate reachable_definitions(EssaNodeDefinition def) {
            Layer::reachable(def.getDefiningNode(), _)
        }

        pragma [noinline]
        private predicate ssa_node_definition_points_to(EssaNodeDefinition def, PenultimateContext context, Object value, ClassObject cls, ObjectOrCfg origin) {
            reachable_definitions(def) and
            ssa_node_definition_points_to_unpruned(def, context, value, cls, origin)
        }

        pragma [noinline]
        private predicate ssa_node_refinement_points_to(EssaNodeRefinement def, PenultimateContext context, Object value, ClassObject cls, ObjectOrCfg origin) {
            method_callsite_points_to(def, context, value, cls, origin)
            or
            import_star_points_to(def, context, value, cls, origin)
            or
            attribute_assignment_points_to(def, context, value, cls, origin)
            or
            callsite_points_to(def, context, value, cls, origin)
            or
            argument_points_to(def, context, value, cls, origin)
            or
            attribute_delete_points_to(def, context, value, cls, origin)
            or
            Filters::uni_edged_phi_points_to(def, context, value, cls, origin)
        }

        /** Points-to for normal assignments `def = ...`. */
        pragma [noinline]
        private predicate assignment_points_to(AssignmentDefinition def, PenultimateContext context, Object value, ClassObject cls, ControlFlowNode origin) {
            points_to(def.getValue(), context, value, cls, origin)
        }

        /** Helper for `parameter_points_to` */
        pragma [noinline]
        private predicate positional_parameter_points_to(ParameterDefinition def, PenultimateContext context, Object value, ClassObject cls, ControlFlowNode origin) {
            exists(PenultimateContext caller, ControlFlowNode arg |
                points_to(arg, caller, value, cls, origin) and
                Flow::callsite_argument_transfer(arg, caller, def, context)
            )
            or
            not def.isSelf() and not def.getParameter().isVarargs() and not def.getParameter().isKwargs() and
            context.isRuntime() and value = unknownValue() and cls = theUnknownType() and origin = def.getDefiningNode()
        }

        /** Points-to for parameter. `def foo(param): ...`. */
        pragma [noinline]
        private predicate parameter_points_to(ParameterDefinition def, PenultimateContext context, Object value, ClassObject cls, ControlFlowNode origin) {
            context.appliesToScope(def.getScope()) and
            context.isRuntime() and
            default_or_special_parameter_points_to(def, value, cls, origin)
            or
            positional_parameter_points_to(def, context, value, cls, origin)
        }

        /** Helper for parameter_points_to */
        private predicate default_or_special_parameter_points_to(ParameterDefinition def, Object value, ClassObject cls, ControlFlowNode origin) {
            exists(ControlFlowNode param |
                param = def.getDefiningNode() |
                exists(PenultimateContext imp | imp.isImport() | points_to(def.getDefault(), imp, value, cls, origin))
                or
                varargs_points_to(param, cls) and value = theEmptyTupleObject() and origin = param
                or
                varargs_points_to(param, cls) and value = param and origin = param
                or
                kwargs_points_to(param, cls) and value = param and origin = param
            )
        }

        /** Holds if the `(obj, caller)` pair matches up with `(self, callee)` pair across call. */
        pragma [noinline]
        private predicate callsite_self_argument_transfer(EssaVariable obj, PenultimateContext caller, ParameterDefinition self, PenultimateContext callee) {
            self.isSelf() and
            exists(CallNode call, PyFunctionObject meth |
                meth.getParameter(0) = self and
                callee.fromCall(call, meth, caller) |
                Calls::plain_method_call(meth, caller, call) and
                obj.getASourceUse() = call.getFunction().(AttrNode).getObject()
                or
                Calls::super_method_call(caller, call, obj, meth)
            )
        }

        /** Points-to for self parameter: `def meth(self, ...): ...`. */
        pragma [noinline]
        private predicate self_parameter_points_to(ParameterDefinition def, PenultimateContext context, Object value, ClassObject cls, ControlFlowNode origin) {
            def.isSelf() and
            exists(FunctionObject meth, Function scope |
                meth.getFunction() = scope and
                def.getDefiningNode().getScope() = scope and
                context.isRuntime() and context.appliesToScope(scope) and
                scope.getScope() = cls.getPyClass() and
                not Layer0PointsTo::Types::abstract_class(cls) and
                value = def.getDefiningNode() and origin = value and
                /* We want to allow decorated function, otherwise we loose a lot of useful information.
                 * However, we want to exclude any function whose arguments are permutated by the decorator.
                 * In general we can't do that, but we can special case the most common ones.
                 */
                not Layer0PointsTo::points_to(scope.getADecorator().getAFlowNode(), _, theStaticMethodType(), _, _) and
                not Layer0PointsTo::points_to(scope.getADecorator().getAFlowNode(), _, theClassMethodType(), _, _)
            )
            or
            exists(EssaVariable obj, PenultimateContext caller |
                ssa_variable_points_to(obj, caller, value, cls, origin) and
                callsite_self_argument_transfer(obj, caller, def, context)
            )
        }

        /** Points-to for deletion: `del name`. */
        pragma [noinline]
        private predicate delete_points_to(DeletionDefinition def, PenultimateContext context, Object value, ClassObject cls, ControlFlowNode origin) {
            value = undefinedVariable() and cls = theUnknownType() and origin = def.getDefiningNode() and context.appliesToScope(def.getScope())
        }

        /** Implicit "definition" of the names of submodules at the start of an `__init__.py` file.
         *
         * Penultimate isn't exactly how the interpreter works, but is the best approximation we can manage statically.
         */
        pragma [noinline]
        private predicate implicit_submodule_points_to(ImplicitSubModuleDefinition def, PenultimateContext context, Object value, ClassObject cls, ObjectOrCfg origin) {
            exists(PackageObject package |
                package.getInitModule().getModule() = def.getDefiningNode().getScope() |
                value = package.submodule(def.getSourceVariable().getName()) and
                cls = theModuleType() and
                origin = value and
                context.isImport()
            )
        }

        /** Implicit "definition" of `__name__` at the start of a module. */
        pragma [noinline]
        private predicate module_name_points_to(ImplicitModuleNameDefinition def, PenultimateContext context, Object value, ClassObject cls, ObjectOrCfg origin) {
            cls = theStrType() and
            origin = def.getDefiningNode() and
            (
                value = object_for_string(def.getName()) and context.isImport()
                or
                value = object_for_string("__main__") and context.isMain() and context.appliesToScope(def.getScope())
            )
        }

        /** Points-to for implicit variable declarations at scope-entry. */
        pragma [noinline]
        private predicate scope_entry_points_to(ScopeEntryDefinition def, PenultimateContext context, Object value, ClassObject cls, ObjectOrCfg origin) {
            /* Transfer from another scope */
            exists(EssaVariable var, PenultimateContext outer |
                Flow::scope_entry_value_transfer(var, outer, def, context) and
                ssa_variable_points_to(var, outer, value, cls, origin)
            )
            or
            /* Undefined variable */
            exists(Scope scope |
                def.getScope() = scope and context.appliesToScope(scope) |
                def.getSourceVariable() instanceof GlobalVariable and scope instanceof Module
                or
                def.getSourceVariable() instanceof LocalVariable and (context.isImport() or context.isRuntime() or context.isMain())
            ) and
            value = undefinedVariable() and cls = theUnknownType() and origin = def.getDefiningNode()
        }

        /** Points-to for a variable (possibly) redefined by a call:
         * `var = ...; foo(); use(var)`
         * Where var may be redefined in call to `foo` if `var` escapes (is global or non-local).
         */
        pragma [noinline]
        private predicate callsite_points_to(CallsiteRefinement def, PenultimateContext context, Object value, ClassObject cls, ObjectOrCfg origin) {
            exists(EssaVariable var, PenultimateContext callee |
                Flow::callsite_exit_value_transfer(var, callee, def, context) and
                ssa_variable_points_to(var, callee, value, cls, origin)
            )
            or
            ssa_variable_points_to(def.getInput(), context, value, cls, origin) and
            (
                // There is no identifiable callee
                not Layer0PointsTo::get_a_call(_, _) = def.getDefiningNode() or
                // An identifiable callee is a builtin
                exists(BuiltinCallable opaque | Layer0PointsTo::get_a_call(opaque, _) = def.getDefiningNode()) or
                // An identifiable callee is a Python function, that is not tracked and does not obviously modify the variable
                context.untrackableCall(def.getCall()) and not
                exists(PyFunctionObject modifier |
                    Layer0PointsTo::get_a_call(modifier, _) = def.getDefiningNode() and
                    modifier.getFunction().getBody().contains(def.getSourceVariable().(Variable).getAStore())
                )
            )
        }

        /** Pass through for `self` for the implicit re-definition of `self` in `self.foo()`. */
        private predicate method_callsite_points_to(MethodCallsiteRefinement def, PenultimateContext context, Object value, ClassObject cls, ObjectOrCfg origin) {
            /* The value of self remains the same, only the attributes may change */
            ssa_variable_points_to(def.getInput(), context, value, cls, origin)
        }

        /** Points-to for `from ... import *`. */
        private predicate import_star_points_to(ImportStarRefinement def, PenultimateContext context, Object value, ClassObject cls, ObjectOrCfg origin) {
            exists(ModuleObject mod, string name |
                Flow::module_and_name_for_import_star(mod, name, def, context) |
                /* Attribute from imported module */
                module_exports(mod, name) and
                Layer::module_attribute_points_to(mod, name, value, cls, origin)
            )
            or
            exists(EssaVariable var |
                /* Retain value held before import */
                Flow::variable_not_redefined_by_import_star(var, context, def) and
                ssa_variable_points_to(var, context, value, cls, origin)
            )
        }

        /** Attribute assignments have no effect as far as value tracking is concerned, except for `__class__`. */
        pragma [noinline]
        private predicate attribute_assignment_points_to(AttributeAssignment def, PenultimateContext context, Object value, ClassObject cls, ObjectOrCfg origin) {
            if def.getName() = "__class__" then
                ssa_variable_points_to(def.getInput(), context, value, _, _) and Layer0PointsTo::points_to(def.getValue(), _, cls, _,_) and
                origin = def.getDefiningNode()
            else
                ssa_variable_points_to(def.getInput(), context, value, cls, origin)
        }

        /** Ignore the effects of calls on their arguments. Penultimate is an approximation, but attempting to improve accuracy would be very expensive for very little gain. */
        pragma [noinline]
        private predicate argument_points_to(ArgumentRefinement def, PenultimateContext context, Object value, ClassObject cls, ObjectOrCfg origin) {
            ssa_variable_points_to(def.getInput(), context, value, cls, origin)
        }

        /** Attribute deletions have no effect as far as value tracking is concerned. */
        pragma [noinline]
        private predicate attribute_delete_points_to(EssaAttributeDeletion def, PenultimateContext context, Object value, ClassObject cls, ObjectOrCfg origin) {
            ssa_variable_points_to(def.getInput(), context, value, cls, origin)
        }

        /* Data flow for attributes. These mirror the "normal" points-to predicates.
         * For each points-to predicate `xxx_points_to(XXX def, PenultimateContext context, Object value, ClassObject cls, ObjectOrCfg origin)`
         * There is an equivalent predicate that tracks the values in attributes:
         * `xxx_named_attribute_points_to(XXX def, PenultimateContext context, string name, Object value, ClassObject cls, ControlFlowNode origin)`
         *  */

        /** INTERNAL -- Public for testing only.
         *
         * Hold if the attribute `name` of the ssa variable `var` refers to `(value, cls, origin)`.
         */
        predicate ssa_variable_named_attribute_points_to(EssaVariable var, PenultimateContext context, string name, Object value, ClassObject cls, ControlFlowNode origin) {
            ssa_definition_named_attribute_points_to(var.getDefinition(), context, name, value, cls, origin)
        }

        /** Helper for `ssa_variable_named_attribute_points_to`. */
        private predicate ssa_definition_named_attribute_points_to(EssaDefinition def, PenultimateContext context, string name, Object value, ClassObject cls, ControlFlowNode origin) {
            ssa_phi_named_attribute_points_to(def, context, name, value, cls, origin)
            or
            ssa_node_definition_named_attribute_points_to(def, context, name, value, cls, origin)
            or
            ssa_node_refinement_named_attribute_points_to(def, context, name, value, cls, origin)
            or
            Filters::ssa_filter_definition_named_attribute_points_to(def, context, name, value, cls, origin)
        }

        /** Holds if the attribute `name` of the ssa phi-function definition `phi` refers to `(value, cls, origin)`. */
        pragma[noinline]
        private predicate ssa_phi_named_attribute_points_to(PhiFunction phi, PenultimateContext context, string name, Object value, ClassObject cls, ControlFlowNode origin) {
            ssa_variable_named_attribute_points_to(phi.getAnInput(), context, name, value, cls, origin)
        }

        /** Helper for `ssa_definition_named_attribute_points_to`. */
        pragma[noinline]
        private predicate ssa_node_definition_named_attribute_points_to(EssaNodeDefinition def, PenultimateContext context, string name, Object value, ClassObject cls, ControlFlowNode origin) {
            assignment_named_attribute_points_to(def, context, name, value, cls, origin)
            or
            delete_named_attribute_points_to(def, context, name, value, cls, origin)
            or
            self_parameter_named_attribute_points_to(def, context, name, value, cls, origin)
            or
            scope_entry_named_attribute_points_to(def, context, name, value, cls, origin)
        }

        /** Helper for `ssa_definition_named_attribute_points_to`. */
        pragma[noinline]
        private predicate ssa_node_refinement_named_attribute_points_to(EssaNodeRefinement def, PenultimateContext context, string name, Object value, ClassObject cls, ControlFlowNode origin) {
            attribute_assignment_named_attribute_points_to(def, context, name, value, cls, origin)
            or
            attribute_delete_named_attribute_points_to(def, context, name, value, cls, origin)
            or
            import_star_named_attribute_points_to(def, context, name, value, cls, origin)
            or
            self_callsite_named_attribute_points_to(def, context, name, value, cls, origin)
            or
            argument_named_attribute_points_to(def, context, name, value, cls, origin)
        }

        pragma[noinline]
        private predicate scope_entry_named_attribute_points_to(ScopeEntryDefinition def, PenultimateContext context, string name, Object value, ClassObject cls, ObjectOrCfg origin) {
            exists(EssaVariable var, PenultimateContext outer |
                Flow::scope_entry_value_transfer(var, outer, def, context) and
                ssa_variable_named_attribute_points_to(var, outer, name, value, cls, origin)
            )
        }

        pragma[noinline]
        private predicate assignment_named_attribute_points_to(AssignmentDefinition def, PenultimateContext context, string name, Object value, ClassObject cls, ControlFlowNode origin) {
            named_attribute_points_to(def.getValue(), context, name, value, cls, origin)
        }

        pragma[noinline]
        private predicate attribute_assignment_named_attribute_points_to(AttributeAssignment def, PenultimateContext context, string name, Object value, ClassObject cls, ControlFlowNode origin) {
            points_to(def.getValue(), context, value, cls, origin) and name = def.getName()
            or
            ssa_variable_named_attribute_points_to(def.getInput(), context, name, value, cls, origin) and not name = def.getName()
        }

        /** Holds if `def` defines the attribute `name`.
         *
         * `def` takes the form `setattr(use, "name")` where `use` is the input to the definition.
         */
        private predicate sets_attribute(ArgumentRefinement def, string name) {
            exists(CallNode call |
                call = def.getDefiningNode() and
                Layer0PointsTo::points_to(call.getFunction(), _, builtin_object("setattr"), _, _) and
                def.getInput().getAUse() = call.getArg(0) and
                call.getArg(1).getNode().(StrConst).getText() = name
            )
        }

        pragma[noinline]
        private predicate argument_named_attribute_points_to(ArgumentRefinement def, PenultimateContext context, string name, Object value, ClassObject cls, ObjectOrCfg origin) {
            if sets_attribute(def, name) then
                points_to(def.getDefiningNode().(CallNode).getArg(2), context, value, cls, origin)
            else
                ssa_variable_named_attribute_points_to(def.getInput(), context, name, value, cls, origin)
        }

        /** Holds if the self variable in the callee (`(var, callee)`) refers to the same object as `def` immediately after the call, (`(def, caller)`). */
        pragma[noinline]
        private predicate callee_self_variable(EssaVariable var, PenultimateContext callee, SelfCallsiteRefinement def, PenultimateContext caller) {
            exists(FunctionObject func, LocalVariable self |
                callee.fromCall(def.getCall(), func, caller) and
                var.reachesExit() and
                var.getSourceVariable() = self and
                self.isSelf() and
                self.getScope() = func.getFunction()
            )
        }

        pragma[noinline]
        private predicate self_callsite_named_attribute_points_to(SelfCallsiteRefinement def, PenultimateContext context, string name, Object value, ClassObject cls, ObjectOrCfg origin) {
            exists(EssaVariable var, PenultimateContext callee |
                ssa_variable_named_attribute_points_to(var, callee, name, value, cls, origin) and
                callee_self_variable(var, callee, def, context)
            )
        }

        /** Gets the (temporally) preceding variable for `self`, e.g. `def` is in method `foo()` and `result` is in `__init__()`.  */
        private EssaVariable preceding_self_variable(ParameterDefinition def) {
            def.isSelf() and
            exists(Function preceding, Function method |
                method = def.getScope() and
                // Only methods
                preceding.isMethod() and preceding.precedes(method) and
                result.reachesExit() and result.getSourceVariable().(Variable).isSelf() and
                result.getScope() = preceding
            )
        }

        pragma [noinline]
        private predicate self_parameter_named_attribute_points_to(ParameterDefinition def, PenultimateContext context, string name, Object value, ClassObject vcls, ControlFlowNode origin) {
            context.isRuntime() and executes_in_runtime_context(def.getScope()) and
            ssa_variable_named_attribute_points_to(preceding_self_variable(def), context, name, value, vcls, origin)
            or
            exists(FunctionObject meth, CallNode call, PenultimateContext caller_context, ControlFlowNode obj |
                meth.getFunction() = def.getScope() and
                method_call(meth, caller_context, call) and
                call.getFunction().(AttrNode).getObject() = obj and
                context.fromCall(call, meth, caller_context) and
                named_attribute_points_to(obj, caller_context, name, value, vcls, origin)
            )
        }

        private predicate delete_named_attribute_points_to(DeletionDefinition def, PenultimateContext context, string name, Object value, ClassObject cls, ControlFlowNode origin) {
            none()
        }

        private predicate attribute_delete_named_attribute_points_to(EssaAttributeDeletion def, PenultimateContext context, string name, Object value, ClassObject cls, ControlFlowNode origin) {
            none()
        }

        /* Helper for import_star_named_attribute_points_to */
        pragma [noinline]
        private predicate star_variable_import_star_module(ImportStarRefinement def, ImportStarNode imp, PenultimateContext context, ModuleObject mod) {
            def.getSourceVariable().getName() = "*" and
            exists(ControlFlowNode fmod |
                fmod = imp.getModule() and
                imp = def.getDefiningNode() and
                points_to(fmod, context, mod, _, _)
            )
        }

        /* Helper for import_star_named_attribute_points_to */
        pragma [noinline]
        private predicate ssa_star_variable_input_points_to(ImportStarRefinement def, PenultimateContext context, string name, Object value, ClassObject cls, ControlFlowNode origin) {
            exists(EssaVariable var |
                ssa_star_import_star_input(def, var) and
                ssa_variable_named_attribute_points_to(var, context, name, value, cls, origin)
            )
        }

        /* Helper for ssa_star_variable_input_points_to */
        pragma [noinline]
        private predicate ssa_star_import_star_input(ImportStarRefinement def, EssaVariable var) {
            def.getSourceVariable().getName() = "*" and var = def.getInput()
        }

        pragma [noinline]
        private predicate import_star_named_attribute_points_to(ImportStarRefinement def, PenultimateContext context, string name, Object value, ClassObject cls, ControlFlowNode origin) {
            exists(ImportStarNode imp, ModuleObject mod |
                star_variable_import_star_module(def, imp, context, mod) |
                if module_exports(mod, name) then (
                    /* Attribute from imported module */
                    exists(ObjectOrCfg obj |
                        Layer::module_attribute_points_to(mod, name, value, cls, obj) and
                        not exists(Variable v | v.getId() = name and v.getScope() = imp.getScope()) and
                        origin = origin_from_object_or_here(obj, imp)
                    )
                ) else (
                    /* Retain value held before import */
                    ssa_star_variable_input_points_to(def, context, name, value, cls, origin)
                )
            )
        }

    }

    private module Filters {

        /** Holds if `expr` is the operand of a unary `not` expression. */
        private ControlFlowNode not_operand(ControlFlowNode expr) {
            expr.(UnaryExprNode).getNode().getOp() instanceof Not and
            result = expr.(UnaryExprNode).getOperand()
        }

        /** Gets the value that `expr` evaluates to (when converted to a boolean) when `use` refers to `(val, cls, origin)`
         * and `expr` contains `use` and both are contained within a test. */
        pragma [nomagic]
        boolean evaluates_boolean(ControlFlowNode expr, ControlFlowNode use, PenultimateContext context, Object val, ClassObject cls, ControlFlowNode origin) {
            contains_interesting_expression_within_test(expr, use) and
            result = evaluates_boolean_unbound(expr, use, val, cls) and
            points_to(use, context, val, cls, origin)
            or
            result = evaluates_boolean(not_operand(expr), use, context, val, cls, origin).booleanNot()
        }

        /** Holds if meaningful equality tests can be made with `o`.
         * Penultimate is true for basic objects like 3 or None, but it is also true for sentinel objects.
         */
        predicate equatable_value(Object o) {
            comparable_value(o)
            or
            o.(ControlFlowNode).getScope() instanceof Module and
            exists(ClassObject c |
                c.isBuiltin() and
                Layer0PointsTo::points_to(o.(CallNode).getFunction(), _, c, _, _)
            )
        }

        /** Holds if meaningful comparisons can be made with `o`.
         * Penultimate is true for basic objects like 3 or None.
         */
        predicate comparable_value(Object o) {
            o.isBuiltin() and not o = unknownValue() and not o = undefinedVariable()
            or
            exists(o.booleanValue())
        }

        /**  Gets the value that `expr` evaluates to (when converted to a boolean) when `use` refers to `(val, cls)`.
         *  Leaves val and cls unbound. */
        private
        pragma[inline]
        boolean evaluates_boolean_unbound(ControlFlowNode expr, ControlFlowNode use, Object val, ClassObject cls) {
            exists(ControlFlowNode clsNode, ClassObject scls |
                BaseFilters::issubclass(expr, clsNode, use) and
                Layer0PointsTo::points_to(clsNode, _, scls, _, _) |
                scls = Layer0PointsTo::Types::get_an_improper_super_type(val) and result = true
                or
                not scls = Layer0PointsTo::Types::get_an_improper_super_type(val) and result = false
            )
            or
            exists(ControlFlowNode clsNode |
                BaseFilters::isinstance(expr, clsNode, use) |
                exists(ClassObject scls |
                    Layer0PointsTo::points_to(clsNode, _, scls, _, _) |
                    scls = Layer0PointsTo::Types::get_an_improper_super_type(cls) and result = true
                    or
                    not scls = Layer0PointsTo::Types::get_an_improper_super_type(cls) and result = false
                )
                or exists(TupleObject t, ClassObject scls |
                    Layer0PointsTo::points_to(clsNode, _, t, _, _) and
                    scls = Layer0PointsTo::Types::get_an_improper_super_type(cls) and result = true
                    |
                    scls = t.getBuiltinElement(_)
                    or
                    Layer0PointsTo::points_to(t.getSourceElement(_), _, scls, _, _)
                )
            )
            or
            exists(ControlFlowNode r,  boolean sense |
                BaseFilters::equality_test(expr, use, sense, r) |
                exists(Object other |
                    /* Must be discrete values, not just types of things */
                    equatable_value(val) and equatable_value(other) and
                    Layer0PointsTo::points_to(r, _, other, _, _) |
                    other != val and result = sense.booleanNot()
                    or
                    other = val and result = sense
                )
            )
            or
            exists(ControlFlowNode l, ControlFlowNode r, boolean sense |
                BaseFilters::equality_test(expr, l, sense, r) |
                exists(int il, int ir |
                    il = evaluates_int(l, use, val) and ir = simple_int_value(r)
                    |
                    result = sense and il = ir
                    or
                    result = sense.booleanNot() and il != ir
                )
            )
            or
            BaseFilters::is_callable(expr, use) and
            (
                Types::class_has_attribute(cls, "__call__") and result = true
                or
                not Layer0PointsTo::Types::class_has_attribute(cls, "__call__") and result = false
            )
            or
            exists(string name |
                BaseFilters::hasattr(expr, use, name) |
                Types::class_has_attribute(cls, name) and result = true
                or
                not Layer0PointsTo::Types::class_has_attribute(cls, name) and result = false
            )
            or
            expr = use and val.booleanValue() = result
            or
            expr = use and Types::instances_always_true(cls) and result = true
            or
            evaluates_int(expr, use, val) = 0 and result = false
            or
            evaluates_int(expr, use, val) != 0 and result = true
        }

        /** Holds if the test on `use` is a test that we can potentially understand */
        private predicate comprehensible_test(ControlFlowNode test, ControlFlowNode use) {
            BaseFilters::issubclass(test, _, use)
            or
            BaseFilters::isinstance(test, _, use)
            or
            BaseFilters::equality_test(test, use, _, _)
            or
            exists(ControlFlowNode l |
                BaseFilters::equality_test(test, l, _, _) |
                exists(evaluates_int(l, use, _))
            )
            or
            BaseFilters::is_callable(test, use)
            or
            BaseFilters::hasattr(test, use, _)
            or
            test = use
            or
            exists(evaluates_int(test, use, _))
            or
            comprehensible_test(not_operand(test), use)
        }


        /** Gets the simple integer value of `f` for numeric literals. */
        private int simple_int_value(ControlFlowNode f) {
            exists(NumericObject num |
                Layer0PointsTo::points_to(f, _, num, _, _) and
                result = num.intValue()
            )
        }

        /** Gets the integer value that `expr` evaluates to given that `use` refers to `val` and `use` is a part of `expr`.
         * Only applies to numeric literal and `len()` of sequences. */
        pragma [inline]
        private int evaluates_int(ControlFlowNode expr, ControlFlowNode use, Object val) {
            exists(CallNode call |
                call = expr and
                Layer0PointsTo::points_to(call.getFunction(), _, theLenFunction(), _, _) and
                use = call.getArg(0) and
                val.(SequenceObject).getLength() = result
            )
            or
            expr = use and result = val.(NumericObject).intValue()
        }

        /** Holds if ESSA edge refinement, `def`, refers to `(value, cls, origin)`. */
        predicate ssa_filter_definition_points_to(PyEdgeRefinement def, PenultimateContext context, Object value, ClassObject cls, ObjectOrCfg origin) {
            exists(ControlFlowNode test, ControlFlowNode use |
                refinement_test(test, use, test_evaluates_boolean(test, use, context, value, cls, origin), def)
            )
            or
            /* If we can't understand the test, assume that value passes through.
             * Or, if the value is `unknownValue()` then let it pass through as well. */
            exists(ControlFlowNode test, ControlFlowNode use |
                refinement_test(test, use, _, def) and
                ssa_variable_points_to(def.getInput(), context, value, cls, origin) |
                not comprehensible_test(test, use) or value = unknownValue()
            )
        }

        /** Holds if ESSA definition, `uniphi`, refers to `(value, cls, origin)`. */
        pragma [noinline]
        predicate uni_edged_phi_points_to(SingleSuccessorGuard uniphi, PenultimateContext context, Object value, ClassObject cls, ObjectOrCfg origin) {
            exists(ControlFlowNode test, ControlFlowNode use |
                /* Because calls such as `len` may create a new variable, we need to go via the source variable
                 * That is perfectly safe as we are only dealing with calls that do not mutate their arguments.
                 */
                use = uniphi.getInput().getSourceVariable().(Variable).getAUse() and
                test = uniphi.getDefiningNode() and
                uniphi.getSense() = test_evaluates_boolean(test, use, context, value, cls, origin)
            )
        }

        /** Holds if the named attibute of ESSA edge refinement, `def`, refers to `(value, cls, origin)`. */
        pragma[noinline]
        predicate ssa_filter_definition_named_attribute_points_to(PyEdgeRefinement def, PenultimateContext context, string name, Object value, ClassObject cls, ObjectOrCfg origin) {
            exists(ControlFlowNode test, AttrNode use, boolean sense |
                edge_refinement_attr_use_sense(def, test, use, name, sense) and
                sense = test_evaluates_boolean(test, use, context, value, cls, origin)
            )
            or
            exists(EssaVariable input |
                input = def.getInput() and
                not edge_refinement_test(def, input, name) and
                SSA::ssa_variable_named_attribute_points_to(input, context, name, value, cls, origin)
            )
        }

        /* Helper for ssa_filter_definition_named_attribute_points_to 
         * Holds if `use` is of the form `var.name` in the test of `def`, and `var` is the source variable of `def`, and `def` has sense `sense`.
         */
        pragma[noinline]
        private predicate edge_refinement_attr_use_sense(PyEdgeRefinement def, ControlFlowNode test, AttrNode use, string name, boolean sense) {
            def.getSense() = sense and
            exists(EssaVariable input |
                input = def.getInput() and
                test = def.getTest() and
                use.getObject(name) = def.getInput().getSourceVariable().(Variable).getAUse() and
                test_contains(test, use)
            )
        }

        /* Helper for ssa_filter_definition_named_attribute_points_to */
        pragma[noinline]
        private predicate edge_refinement_test(PyEdgeRefinement def, EssaVariable input, string name) {
            exists(ControlFlowNode test |
                input = def.getInput() and
                test = def.getTest() |
                exists(AttrNode use |
                    refinement_test(test, use.getObject(name), _, def)
                )
            )
        }

    }

    
    module Types {

         /** INTERNAL -- Use `ClassObject.getBaseType(n)` instead.
          *
          * Gets the nth base class of the class. */
         
         Object class_base_type(ClassObject cls, int n) {
             exists(ClassExpr cls_expr | cls.getOrigin() = cls_expr |
                 points_to(cls_expr.getBase(n).getAFlowNode(), _, result, _, _)
                 or
                 is_new_style(cls) and not exists(cls_expr.getBase(0)) and result = theObjectType() and n = 0
             )
             or
             result = builtin_base_type(cls) and n = 0
         }

        private int class_base_count(ClassObject cls) {
            exists(ClassExpr cls_expr |
                cls.getOrigin() = cls_expr |
                result = strictcount(cls_expr.getABase())
                or
                is_new_style_bool(cls) = true and not exists(cls_expr.getBase(0)) and result = 1
                or
                is_new_style_bool(cls) = false and not exists(cls_expr.getBase(0)) and result = 0
            )
            or
            cls = theObjectType() and result = 0
            or
            exists(builtin_base_type(cls)) and not cls = theObjectType() and result = 1
        }


        private boolean is_new_style_bool(ClassObject cls) {
            major_version() = 3 and result = true
            or
            cls.isBuiltin() and result = true
            or
            major_version() = 2 and
            if Layer::has_explicit_metaclass(cls) then
                result = true
            else
                result = is_new_style_bool(cls, 0)
        }

        private boolean is_new_style_bool(ClassObject cls, int n) {
            major_version() = 2 and
            exists(ClassExpr cls_expr |
                cls.getOrigin() = cls_expr and
                n = count(cls_expr.getABase()) |
                result = false
            )
            or
            result = is_new_style_bool(cls, n+1).booleanOr(is_new_style_bool(class_base_type(cls, n)))
        }

        /** INTERNAL -- Use `ClassObject.isNewStyle()` instead. */
        
        predicate is_new_style(ClassObject cls) {
            class_base_type(cls, _) = theObjectType()
            or
            is_new_style_bool(cls) = true
        }

         /** INTERNAL -- Do not use */
         private predicate mro_sparse(ClassObject cls, ClassObject sup, int index) {
             if Layer0PointsTo::Types::is_new_style(sup) then (
                 depth_first_indexed(cls, sup, index) and
                 not exists(int after | depth_first_indexed(cls, sup, after) and after > index)
             ) else (
                 depth_first_indexed(cls, sup, index) and
                 not exists(int before | depth_first_indexed(cls, sup, before) and before < index)
             )
         }

         /** An index for the base class in the MRO such that the index for superclasses of the base
          * class are guaranteed not to clash with the superclasses of other base classes.  */
         private predicate class_base_offset(ClassObject cls, ClassObject base, int index) {
             exists(int n |
                 Layer0PointsTo::Types::class_base_type(cls, n) = base |
                 index = sum(ClassObject left_base |
                     exists(int i | left_base = Layer0PointsTo::Types::class_base_type(cls, i) and i < n) |
                     count (Layer0PointsTo::Types::get_an_improper_super_type(left_base))
                 )
             )
         }

         /** Index all super-classes using depth-first search,
          * numbering parent nodes before their children. */
         private predicate depth_first_indexed(ClassObject cls, ClassObject sup, int index) {
             not has_illegal_bases(cls) and Layer0PointsTo::Types::get_an_improper_super_type(cls) = sup and
             (
                 sup = cls and index = 0
                 or
                 exists(ClassObject base, int base_offset, int sub_index |
                     base = Layer0PointsTo::Types::class_base_type(cls, _) and
                     class_base_offset(cls, base, base_offset) and
                     depth_first_indexed(base, sup, sub_index) and
                     index = base_offset + sub_index + 1
                 )
             )
         }

         /** INTERNAL -- Use `ClassObject.getASuperType()` instead. */
         
         ClassObject get_a_super_type(ClassObject cls) {
             result = class_base_type(cls, _)
             or
             result = class_base_type(get_a_super_type(cls), _)
         }

         /** INTERNAL -- Use `ClassObject.getAnImproperSuperType()` instead. */
         
         ClassObject get_an_improper_super_type(ClassObject cls) {
             result = cls
             or
             result = get_a_super_type(cls)
         }


         /** Class `cls` has duplicate base classes. */
         private predicate has_duplicate_bases(ClassObject cls) {
             exists(ClassObject base, int i, int j | i != j and base = Layer0PointsTo::Types::class_base_type(cls, i) and base = Layer0PointsTo::Types::class_base_type(cls, j))
         }

         private predicate has_illegal_bases(ClassObject cls) {
             has_duplicate_bases(cls) or Layer0PointsTo::Types::get_an_improper_super_type(Layer0PointsTo::Types::class_base_type(cls, _)) = cls
         }

         /** INTERNAL -- Use `ClassObject.getMroItem(index)` instead. */
         
         ClassObject get_mro_item(ClassObject cls, int index) {
             /* Collapse the sparse array into a dense one */
             exists(int idx | mro_sparse(cls, result, idx) |
                 idx = rank[index](int i, ClassObject s | mro_sparse(cls, s, i) | i)
             )
         }

         /** INTERNAL -- Use `ClassObject.nextInMro(sup)` instead. */
         
         ClassObject next_in_mro(ClassObject cls, ClassObject sup) {
             exists(int i |
                 sup = get_mro_item(cls, i) and
                 result = get_mro_item(cls, i+1)
             )
         }

         private int declaring_class_index(ClassObject cls, string name) {
             class_declares_attribute(get_mro_item(cls, result), name)
         }

         /** INTERNAL -- Use `ClassObject.lookupMro(start, name)` instead. */
         
         predicate class_lookup_in_mro(ClassObject cls, ClassObject start, string name, Object object) {
             exists(int i, int j |
                 start = get_mro_item(cls, i) and
                 j = declaring_class_index(cls, name) and j >= i and
                 not exists(int k | k = declaring_class_index(cls, name) and k >= i and k < j) and
                 class_declared_attribute(get_mro_item(cls, j), name, object, _, _)
             )
         }

         /** INTERNAL -- Use `ClassObject.declaredAttribute(name). instead. */
         
         predicate class_declared_attribute(ClassObject owner, string name, Object value, ClassObject vcls, ObjectOrCfg origin) {
             /* Note that src_var must be a local variable, we aren't interested in the value that any global variable may hold */
              not value = undefinedVariable() and
              exists(EssaVariable var, LocalVariable src_var |
                 var.getSourceVariable() = src_var and
                 src_var.getId() = name and
                 var.getAUse() = owner.getImportTimeScope().getANormalExit() |
                 Layer0PointsTo::ssa_variable_points_to(var, _, value, vcls, origin)
             )
             or
             value = builtin_class_attribute(owner, name) and class_declares_attribute(owner, name) and
             origin = value and vcls = builtin_object_type(value)
         }

        private predicate possible_attribute(ClassObject cls, string name) {
            exists(ClassObject sub |
                get_an_improper_super_type(sub) = cls and
                class_declares_attribute(get_an_improper_super_type(sub), name)
            )
        }

        pragma [nomagic]
        private boolean class_has_attribute_from_base(ClassObject cls, int n, string name) {
           n = class_base_count(cls) and possible_attribute(cls, name) and result = false
           or
           exists(ClassObject baseN |
               baseN = class_base_type(cls, n) |
               true = class_has_non_object_attribute_bool(baseN, name) and result = true
               or
               true = class_has_attribute_from_base(cls, n+1, name) and result = true
               or
               false = class_has_non_object_attribute_bool(baseN, name) and false = class_has_attribute_from_base(cls, n+1, name) and result = false
               or
               baseN = theObjectType() and result = class_has_attribute_from_base(cls, n+1, name)
           )
        }

        /** Holds if the class `cls` has an attribute called `name` */
        
        predicate class_has_attribute(ClassObject cls, string name) {
            class_declares_attribute(get_an_improper_super_type(cls), name)
        }

        /** Holds if `cls` has an attribute `name` that is not derived from `object` */
        pragma [noinline]
        private boolean class_has_non_object_attribute_bool(ClassObject cls, string name) {
            class_declares_attribute(cls, name) and not cls = theObjectType() and result = true
            or
            not class_declares_attribute(cls, name) and result = class_has_attribute_from_base(cls, 0, name)
        }

        /** Holds if `defn` is the class containing the definition of attribute `name` when considering only the base classes
         * number `n` and upward of class `cls`. For example given `class C(B0, B1): pass` where both `B1` and `B2` defined `name`
         * then `(C, name, 1, B1)` and `(C, name, 0, B0)` both hold. Penultimate is a conservative approximation.
         */
        pragma [noopt]
        private predicate class_attribute_defining_class_for_base(ClassObject cls, string name, int n, ClassObject defn) {
            exists(ClassObject baseN |
                baseN = class_base_type(cls, n)
                |
                class_declares_attribute(baseN, name) and defn = baseN
                or
                exists(int np1 |
                    np1 = n + 1 and
                    class_attribute_defining_class_for_base(cls, name, np1, defn)
                ) and
                false = class_has_non_object_attribute_bool(baseN, name)
                or
                exists(int np1 |
                    np1 = n + 1 and
                    false = class_has_attribute_from_base(cls, np1, name)
                ) and
                class_attribute_defining_class(baseN, name, defn)
            )
        }

        /** Holds if `defn` is the class containing the definition of attribute `name` for class `cls`. 
         * Penultimate is a conservative approximation.
         */
        pragma [noinline] 
        private predicate class_attribute_defining_class(ClassObject cls, string name, ClassObject defn) {
            if class_declares_attribute(cls, name) then
                defn = cls
            else
                class_attribute_defining_class_for_base(cls, name, 0, defn)
        }

         /** INTERNAL -- Use `ClassObject.attributeRefersTo(name, value, vlcs, origin). instead.
          */
         
         predicate class_attribute_lookup(ClassObject cls, string name, Object value, ClassObject vcls, ObjectOrCfg origin) {
            exists(ClassObject defn |
                class_attribute_defining_class(cls, name, defn) and
                class_declared_attribute(defn, name, value, vcls, origin)
            )
            or
            false = class_has_non_object_attribute_bool(cls, name) and
            class_declared_attribute(theObjectType(), name, value, vcls, origin)
            or
            /* Exactly two base classes and both define the same attribute.
             */
            class_base_count(cls) = 2 and
            exists(ClassObject base1, ClassObject base2 |
                base1 = class_base_type(cls, 0) and
                base2 = class_base_type(cls, 1) and
                class_attribute_lookup(base1, name, value, vcls, origin) and
                class_attribute_lookup(base2, name, value, vcls, origin)
            )
         }


         /** INTERNAL -- Use `ClassObject.failedInference(reason). instead.
          *
          *  Holds if type inference failed to compute the full class hierarchy for this class for the reason given. */
         
         predicate failed_inference(ClassObject cls, string reason) {
             strictcount(cls.getPyClass().getADecorator()) > 1 and reason = "Multiple decorators"
             or
             exists(cls.getPyClass().getADecorator()) and not six_add_metaclass(_, cls, _) and reason = "Decorator not understood"
             or
             exists(int i |
                 exists(((ClassExpr)cls.getOrigin()).getBase(i)) and reason = "Missing base " + i
                 |
                 not exists(class_base_type(cls, i)) or class_base_type(cls, i) = unknownValue()
             )
             or
             exists(cls.getPyClass().getMetaClass()) and not exists(Layer::class_explicit_metaclass(cls)) and reason = "Failed to infer metaclass"
             or
             exists(int i | failed_inference(class_base_type(cls, i), _) and reason = "Failed inference for base class at position " + i)
             or
             exists(int i | strictcount(class_base_type(cls, i)) > 1 and reason = "Multiple bases at position " + i)
             or
             cls = theUnknownType() and reason = "Unknown Type"
         }

         /** INTERNAL -- Use `ClassObject.getMetaClass()` instead.
          *
          *  Gets the metaclass for this class */
         
         ClassObject class_get_meta_class(ClassObject cls) {
             result = Layer::class_get_meta_class_candidate(cls) and
             forall(ClassObject meta |
                 meta = Layer0PointsTo::Layer::class_get_meta_class_candidate(cls) |
                 meta = get_an_improper_super_type(result)
             )
         }

         private Object six_add_metaclass_function() {
             exists(ModuleObject six |
                 six.getName() = "six" and
                 Layer::module_attribute_points_to(six, "add_metaclass", result, _, _)
             )
         }

         /** INTERNAL -- Do not use */
         
         predicate six_add_metaclass(CallNode decorator_call, ClassObject decorated, ControlFlowNode metaclass) {
             exists(CallNode decorator |
                 decorator_call.getArg(0) = decorated and
                 decorator = decorator_call.getFunction() and
                 decorator.getArg(0) = metaclass |
                 points_to(decorator.getFunction(), _, six_add_metaclass_function(), _, _)
                 or
                 exists(ModuleObject six |
                    six.getName() = "six" and
                    points_to(decorator.getFunction().(AttrNode).getObject("add_metaclass"), _, six, _, _)
                )
             )
         }

         /** INTERNAL -- Use `cls.isAbstract()` instead. */
         
         predicate abstract_class(ClassObject cls) {
             Types::class_get_meta_class(cls) = theAbcMetaClassObject()
             or
             exists(FunctionObject unimplemented, Raise r, Name ex |
                 class_attribute_lookup(cls, _, unimplemented, _, _) and
                 r.getScope() = unimplemented.getFunction() and
                 (r.getException() = ex or r.getException().(Call).getFunc() = ex) and
                 (ex.getId() = "NotImplementedError" or ex.getId() = "NotImplemented")
             )
         }

         /** Holds if instances of class `cls` are always truthy. */
         
         predicate instances_always_true(ClassObject cls) {
             not cls = theNoneType() and
             not exists(ClassObject decl, string meth |
                 meth = "__bool__" or meth = "__len__" or
                 meth = "__nonzero__" and major_version() = 2 |
                 not decl = theObjectType() and
                 decl = Layer0PointsTo::Types::get_an_improper_super_type(cls) and
                 class_declares_attribute(decl, meth)
             )
         }

    }

    /** INTERNAL -- Public for testing only */
    module Test {

        import Calls
        import SSA
        import Layer

    }

}