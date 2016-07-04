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
import semmle.python.types.Version

/** An ImportTimeScope is any scope that is not nested within a function and will thus be executed if its
 * enclosing module is imported. 
 * Note however, that if a scope is not an ImportTimeScope it may still be executed at import time.
 * This is an artificial approximation, which is necessary for static analysis.
 */
class ImportTimeScope extends Scope {
 
    ImportTimeScope() {
        not this.getScope*() instanceof Function
    }

    /** Return the Object(s) which can be bound to 'name' upon completion of the code defining this namespace */
    cached predicate objectReachingExit(string name, Object value, ControlFlowNode origin) {
        exists(SsaVariable var | var.getAUse() = this.getANormalExit() and var.getId() = name |
            ssa_points_to(var.getAnUltimateDefinition(), value, origin)
        )
        or
        import_star_defines_object(this, name, value, origin)
    }
    
    /** Whether this scope defines 'name' */
    cached predicate definesName(string name) {
        exists(SsaVariable var | name = var.getId() and var.getAUse() = this.getANormalExit())
        or
        import_star_defines_name(this, name)
    }
  
}

/** Simple points to with no guards analysis and ignoring operator expressions, except version and os tests. */
cached predicate simple_points_to(ControlFlowNode f, Object obj) {
    top_level(f) and
    (
      obj = f and (
        f.isLiteral() and not f.getNode() instanceof ImmutableLiteral
        or
        f.isFunction()
        or
        f.isClass()
        or
        f instanceof VersionTest
        or
        f instanceof OsTest
      )
      or
      f.isLiteral() and obj = f.getNode().(ImmutableLiteral).getLiteralObject()
      or
      simple_use_points_to(f, obj)
      or
      simple_def_points_to(f, obj)
      or
      simple_attribute_points_to(f, obj)
      or
      simple_import_points_to(f, obj)
      or
      simple_import_member_points_to(f, obj)
      or
      simple_if_exp_points_to(f, obj)
    )
}

/** INTERNAL -- Use f.refersTo(obj, _) instead */
predicate simple_use_points_to(ControlFlowNode f, Object obj) {
    simple_class_use_points_to(f, obj)
    or
    simple_module_use_points_to(f, obj)
}

/** For name lookup in modules:
 *    1. Use the value of the global variable.
 *    2. If the global variable may not be defined, then use the builtin variable.
 */
private predicate simple_module_use_points_to(ControlFlowNode f, Object obj) {
    f.getScope() instanceof Module and 
    (
        exists(SsaVariable var | 
            f = var.getAUse() |
            simple_ssa_points_to(var.getAnUltimateDefinition(), obj)
        )
        or
        not exists(SsaVariable var | f = var.getAUse() and not var.reachableWithoutDefinition()) and
        exists(GlobalVariable gv |
            f.(NameNode).uses(gv) |
            obj = builtin_object(gv.getId())
        )
    )
}

/** For name lookup in classes:
 *    1. Use the locally defined value.
 *    2. If the local variable is not always defined, then use the value of the global variable.
 *    3. If neither of the above are defined, then use the builtin variable.
 */
private predicate simple_class_use_points_to(ControlFlowNode f, Object obj) {
    f.getScope() instanceof Class and 
    (
        /* Is the variable defined locally within the class */
        exists(SsaVariable var |
            f = var.getAUse() and
            simple_ssa_points_to(var.getAnUltimateDefinition(), obj)
        )
        or
        not exists(SsaVariable var | f = var.getAUse() and not var.reachableWithoutDefinition()) and
        exists(Variable v |
            f.(NameNode).uses(v) |
            /* Global (module-level) access */
            exists(SsaVariable ssa |
                ssa = definedAtEntry(f.getScope(), v.getId()) |
                simple_ssa_points_to(ssa.getAnUltimateDefinition(), obj)
            )
            or
            /* Built-in (e.g. 'len') access */
            not exists(SsaVariable ssa | 
                ssa = definedAtEntry(f.getScope(), v.getId()) and 
                not ssa.reachableWithoutDefinition()
            ) and
            obj = builtin_object(v.getId())
        )
    )
}

private predicate simple_ssa_points_to(SsaVariable var, Object obj) {
    exists(ControlFlowNode def | 
        def = var.getDefinition() and
        simple_points_to(def, obj)
    )
}

private predicate simple_def_points_to(DefinitionNode def, Object obj) {
    simple_points_to(def.getValue(), obj)
}

private predicate simple_attribute_points_to(AttrNode f, Object obj) {
    f.isLoad() and
    exists(ControlFlowNode val, string name, Object value |
        val = f.getObject(name) and simple_points_to(val, value) |
        py_cmembers(value, name, obj)
        or
        /* Don't attempt to include non-module attributes here */
        exists(Module m | m = value.getOrigin() |
            simple_python_module_attributes(m, name, obj) 
        ) 
    )
}

private predicate simple_python_module_attributes(Module m, string name, Object obj) {
    exists(SsaVariable var | var.getAUse() = m.getANormalExit() and var.getId() = name |
        simple_ssa_points_to(var.getAnUltimateDefinition(), obj)
    )
    or
    simple_import_star_defines(m, name, obj)
    or
    exists(Module sub | 
        sub = m.getSubModule(name) |
        sub = obj.getOrigin()
    )
}
   
private predicate simple_import_star_defines(Module m, string name, Object obj) {
    exists(ImportStar im, ModuleObject imported_module | 
        has_import_star(m, im, imported_module) |
        simple_module_exports(imported_module.getModule(), name) and
        simple_python_module_attributes(imported_module.getModule(), name, obj)
        or
        py_cmembers(imported_module, name, obj)
    )
}

private predicate simple_module_exports(Module module, string name) {
    module.declaredInAll(name)
    or
    simple_python_module_attributes(module, name, _) and
    not module.declaredInAll(_)
}

predicate simple_module_imported_as(ModuleObject m, string name) {
    exists(ModuleObject p, string mname | 
        simple_module_attribute(p, mname, m) |
        name = p.getName() + "." + mname
    )
    or 
    m.getName() = name
}

private predicate simple_import_member_points_to(ImportMemberNode f, Object obj) {
    exists(string name, ModuleObject module, ImportMember im | 
        im.getAFlowNode() = f and name = im.getName() and
        simple_points_to(f.getModule(name), module) |
        simple_python_module_attributes(module.getModule(), name, obj)
        or
        py_cmembers(module, name, obj)
    )
}

predicate simple_module_attribute(ModuleObject m, string name, Object obj) {
    py_cmembers(m, name, obj)
    or
    simple_python_module_attributes(((PythonModuleObject)m).getModule(), name, obj)
}

private predicate simple_import_points_to(ControlFlowNode f, ModuleObject mod) {
    exists(ImportExpr imp, string name | 
        imp = f.getNode() and name = imp.getImportedModuleName() and
        simple_module_imported_as(mod, name)
    )
}

private predicate simple_if_exp_points_to(IfExprNode f, Object obj) {
    simple_points_to(f.getAnOperand(), obj)
}

/* Points to pruned using guards analysis */

/** INTERNAL -- Whether this CfNode is pruned due to version or OS constraints */
predicate import_time_pruned(ControlFlowNode f) {
    exists(VersionGuard v | 
        v.controls(f.getBasicBlock(), true) and
        v.getVersion() != major_version()
    )
    or
    exists(VersionGuard v |
        v.controls(f.getBasicBlock(), false) and
        v.getVersion() = major_version()
    )
        or
    exists(OsGuard o |
        o.controls(f.getBasicBlock(), true) and
        not py_flags("sys.platform", o.getOs())
    )
    or
    exists(OsGuard o |
        o.controls(f.getBasicBlock(), false) and
        py_flags("sys.platform", o.getOs())
    )
}
 
/** INTERNAL -- Use f.refersTo(obj, _, origin) instead */
cached predicate import_time_points_to(ControlFlowNode f, Object obj, ControlFlowNode origin) {
    top_level(f) and not import_time_pruned(f) and
    (
      obj = f and origin = f and (
        f.isLiteral() and not f.getNode() instanceof ImmutableLiteral
        or
        f.isFunction()
        or
        f.isClass()
      )
      or
      six_add_metaclass(f, obj, _) and origin = obj
      or
      f.isLiteral()and origin = f and obj = f.getNode().(ImmutableLiteral).getLiteralObject()
      or
      call_points_to(f, obj, origin)
      or
      use_points_to(f, obj, origin)
      or
      def_points_to(f, obj, origin)
      or
      attribute_points_to(f, obj, origin)
      or
      import_points_to(f, obj, origin)
      or
      import_member_points_to(f, obj, origin)
      or
      if_exp_points_to(f, obj, origin)
    )
}

private predicate is_instance(ControlFlowNode f, ClassObject cls) {
    exists(Object val | simple_points_to(f, val) and cls = val.simpleClass())
    or
    simple_points_to(f.(CallNode).getFunction(), cls)
}

private predicate call_points_to(CallNode f, Object obj, ControlFlowNode origin) {
    /* There are four possibilities here.
     * 1. `type(known_type)` where we know the class of `known_type` and we know its origin
     * 2. `type(known_type)` where we know the class of `known_type`, 
     *        but we don't know it origin (because its a builtin type)
     * 3. `type(other)` where we don't know the type of `other
     * 4. `func(...)` where func is not know to be `type`.
     * For case 1 we make the origin the origin of the class
     * For cases 2, 3, and 4 we make the origin the call.
     */
    exists(ControlFlowNode func |
        func = f.getFunction() |
        simple_points_to(func, theTypeType()) and is_instance(f.getArg(0), obj) and origin.getNode() = obj.getOrigin()
        or
        simple_points_to(func, theTypeType()) and is_instance(f.getArg(0), obj) and not exists(obj.getOrigin()) and origin = f
        or
        not is_instance(f.getArg(0), _) and obj = f and origin = f
        or
        not simple_points_to(func, theTypeType()) and obj = f and origin = f
    )
}

private predicate use_points_to(ControlFlowNode f, Object obj, ControlFlowNode origin) {
    class_use_points_to(f, obj, origin)
    or
    module_use_points_to(f, obj, origin)
}

/** For name lookup in modules:
 *    1. Use the value of the global variable.
 *    2. If the global variable may not be defined, then use the builtin variable.
 */
private predicate module_use_points_to(ControlFlowNode f, Object obj, ControlFlowNode origin) {
    f.getScope() instanceof Module and 
    (
        exists(SsaVariable var | 
            f = var.getAUse() |
            ssa_points_to(var.getAnUltimateDefinition(), obj, origin)
        )
        or
        not exists(SsaVariable var | f = var.getAUse() and not var.reachableWithoutDefinition()) and
        exists(GlobalVariable gv |
            f.(NameNode).uses(gv) |
            obj = builtin_object(gv.getId()) and origin = f
            or
            import_star_defines_object(f.getScope(), gv.getId(), obj, origin)
        )
    )
}

/** For name lookup in classes:
 *    1. Use the locally defined value.
 *    2. If the local variable is not always defined, then use the value of the global variable.
 *    3. If neither of the above are defined, then use the builtin variable.
 */
private predicate class_use_points_to(ControlFlowNode f, Object obj, ControlFlowNode origin) {
    f.getScope() instanceof Class and 
    (
        exists(SsaVariable var |
            f = var.getAUse() and
            ssa_points_to(var.getAnUltimateDefinition(), obj, origin)
        )
        or
        not exists(SsaVariable var | f = var.getAUse() and not var.reachableWithoutDefinition()) and
        exists(Variable v |
            f.(NameNode).uses(v) |
            exists(SsaVariable ssa |
                ssa = definedAtEntry(f.getScope(), v.getId()) |
                ssa_points_to(ssa.getAnUltimateDefinition(), obj, origin)
            )
            or
            not exists(SsaVariable ssa | 
                ssa = definedAtEntry(f.getScope(), v.getId()) and 
                not ssa.reachableWithoutDefinition()
            ) and
            obj = builtin_object(v.getId()) and origin = f
        )
    )
}

private predicate ssa_points_to(SsaVariable var, Object obj, ControlFlowNode origin) {
    exists(ControlFlowNode def | 
        def = var.getDefinition() and
        import_time_points_to(def, obj, origin)
    )
}

private predicate def_points_to(DefinitionNode def, Object obj, ControlFlowNode origin) {
    import_time_points_to(def.getValue(), obj, origin)
}

private predicate attribute_points_to(AttrNode f, Object obj, ControlFlowNode origin) {
    f.isLoad() and
    exists(ControlFlowNode val, string name, Object value |
        val = f.getObject(name) and import_time_points_to(val, value, _) |
        py_cmembers(value, name, obj) and origin = f
        or
        /* Don't attempt to include non-module attributes here.
          Doing so would cause dependence of the whole points-to library  */
        exists(Module m | m = value.getOrigin() |
            import_time_module_attributes(m, name, obj, origin)
        )
    )
}

/** INTERNAL -- Use m.attributeRefersTo(name, obj, origin) instead */
predicate import_time_py_module_attributes(Module m, string name, Object obj, ControlFlowNode origin) {
    not m.isPackage() and
    (
      exists(SsaVariable var | var.getAUse() = m.getANormalExit() and var.getId() = name |
          ssa_points_to(var.getAnUltimateDefinition(), obj, origin)
      )
      or
      import_star_defines_object(m, name, obj, origin)
      or
      not simple_python_module_attributes(m, "__name__", _) and
      name = "__name__" and obj = object_for_string(m.getName()) and origin = m.getEntryNode()
      or
      /* Set the __package__ to the value specified in the documentation.
       * Note, however, that it is often None in practice as the interpreter sets 
       * the __package__ attribute only when required by the import machinery.
       * We choose the string value in preference to None as it is the steady state value.  
       */
      not simple_python_module_attributes(m, "__package__", _) and name = "__package__" and 
      obj = object_for_string(m.getPackage().getName()) and origin = m.getPackage().getEntryNode()
    )
}

/** INTERNAL -- Use package.attributeRefersTo(name, obj, origin) instead */
predicate import_time_package_attributes(Module package, string name, Object obj, ControlFlowNode origin) {
    package.isPackage() and
    (
      not name = "__name__" and import_time_module_attributes(package.getInitModule(), name, obj, origin)
      or
      name = "__name__" and obj = object_for_string(package.getName()) and origin = package.getEntryNode()
      or
      not simple_python_module_attributes(package.getInitModule(), "__package__", _) and
      name = "__package__" and obj = object_for_string(package.getName()) and origin = package.getEntryNode()
      or
      not package.getInitModule().(ImportTimeScope).definesName(name)
      and
      exists(ModuleObject module |
          module.getModule() = package.getSubModule(name) and
          origin = module.getModule().getEntryNode() and
          obj = module and
          explicitly_imported(module)
      )
    )
}

/** Whether the module is explicitly imported somewhere */
private predicate explicitly_imported(ModuleObject module) {
    exists(ImportExpr ie | import_time_module_imported_as(module, ie.getAnImportedModuleName()))
    or
    exists(ImportMember im | import_time_module_imported_as(module, im.getImportedModuleName()))
}

private predicate import_time_module_attributes(Module m, string name, Object obj, ControlFlowNode origin) {
    import_time_py_module_attributes(m, name, obj, origin)
    or
    import_time_package_attributes(m, name, obj, origin)
}

/** Does an import star exists in Module m that imports a module called 'name', such that the flow from the import reached the module exit. */
private predicate has_import_star(Module m, ImportStar im, ModuleObject imported_module) {
    exists(string name |
        import_time_module_imported_as(imported_module, name) and
        name = im.getImportedModuleName() and
        im.getScope() = m and
        im.getAFlowNode().getBasicBlock().reachesExit()
    )
}

private predicate import_star_defines_object(Module m, string name, Object obj, ControlFlowNode origin) {
    exists(ModuleObject imported_module, ImportStar import_stmt |
        has_import_star(m, import_stmt, imported_module)
        |
        import_time_exports(imported_module.getModule(), name) and
        import_time_module_attributes(imported_module.getModule(), name, obj, origin)
        or
        origin = import_stmt.getAFlowNode() and py_cmembers(imported_module, name, obj)
    ) 
}
    
private predicate import_star_defines_name(Module m, string name) {
    exists(ModuleObject imported_module, ImportStar import_stmt |
        has_import_star(m, import_stmt, imported_module)
        |
        import_time_exports(imported_module.getModule(), name)
        or
        py_cmembers(imported_module, name, _)
    ) 
}
 
/** INTERNAL -- Use m.exports(name) instead */
predicate import_time_exports(Module m, string name) {
    if m.isPackage() then (
        not m.getInitModule().declaredInAll(_) and not name.charAt(0) = "_" and
        exists(ModuleObject sub |
            sub.getModule() = m.getSubModule(name) |
            explicitly_imported(sub)
        )
        or
        import_time_exports(m.getInitModule(), name)
    ) else (
        m.declaredInAll(_) and m.declaredInAll(name)
        or
        not m.declaredInAll(_) and m.(ImportTimeScope).definesName(name) and not name.charAt(0) = "_"
    )
}

/** INTERNAL -- Use m.exportsComplete() instead */
predicate import_time_exports_complete(Module m) {
    not exists(Call modify, Attribute attr, GlobalVariable all | 
        modify.getScope() = m and modify.getFunc() = attr and 
        all.getId() = "__all__" |
        attr.getObject().(Name).uses(all)
    )
}

/** INTERNAL -- Use m.importedAs(name) instead */
predicate import_time_module_imported_as(ModuleObject m, string name) {
    m.getName() = name
    or
    /* sys.modules['name'] = m */
    exists(ControlFlowNode sys_modules_flow, ControlFlowNode n, ControlFlowNode mod |
        /* Use simple points-to here to avoid slowing down the recursion too much */
        exists(SubscriptNode sub, Object sys_modules |
            sub.getValue() = sys_modules_flow and
            simple_points_to(sys_modules_flow, sys_modules) and
            py_cmembers(theSysModuleObject(), "modules", sys_modules) and
            sub.getIndex() = n and
            n.getNode().(StrConst).getText() = name and
            sub.(DefinitionNode).getValue() = mod and
            simple_points_to(mod, m)
        )
    )
}

/** INTERNAL -- May be modified or deleted without warning. */
predicate is_locally_defined_from_dot_import_in_init(ImportMemberNode f, string name) {
    exists(ImportMember im |
        im.getAFlowNode() = f and
        name = im.getName() and
        im.getModule().(ImportExpr).getLevel() = 1 and
        not exists(im.getModule().(ImportExpr).getName()) and
        im.getEnclosingModule().getName().matches("%.\\_\\_init\\_\\_")
    )
}

/** Special case of `from . import name` in an `__init__` module.
 *  In this case the value can be defined in the `__init__` module, 
 *  thus needs to be flow sensitive.
 */
private predicate locally_defined_from_dot_import_in_init(ImportMemberNode f, SsaVariable var) {
    is_locally_defined_from_dot_import_in_init(f, var.getId())
    and var.getDefinition().strictlyDominates(f)
}

private predicate import_member_points_to(ImportMemberNode f, Object obj, ControlFlowNode origin) {
    /* Three options here:
     * 1. The majority of imports.
     * 2. Importing from the package in an __init__ module, that is locally defined
     * 3. Importing from the package in an __init__ module, that is not locally defined
     */
    exists(string name, ModuleObject module, ImportMember im | 
        im.getAFlowNode() = f and name = im.getName() and
        import_time_points_to(f.getModule(name), module, _) |
        import_time_module_attributes(module.getModule(), name, obj, origin)
        or
        origin = f and py_cmembers(module, name, obj)
    ) and 
    not is_locally_defined_from_dot_import_in_init(f, _)
    or
    /* 2. */
    exists(SsaVariable var | 
        locally_defined_from_dot_import_in_init(f, var) and
        ssa_points_to(var, obj, origin)
    )
    or
    /* 3. */
    exists(string name |
        is_locally_defined_from_dot_import_in_init(f, name) and
        not locally_defined_from_dot_import_in_init(f, _) and
        exists(PackageObject package |
            package.getInitModule().getModule() = f.getNode().getEnclosingModule() |
            obj = package.submodule(name) and origin = f
        )
    )
}

private predicate import_points_to(ControlFlowNode f, ModuleObject mod, ControlFlowNode origin) {
    exists(string name, ImportExpr imp | 
        imp = f.getNode() and name = imp.getImportedModuleName() and
        import_time_module_imported_as(mod, name) |
        mod.isC() and origin = f
        or
        not mod.isC() and origin = mod.getModule().getEntryNode()
    )
}

private predicate if_exp_points_to(IfExprNode f, Object obj, ControlFlowNode origin) {
    import_time_points_to(f.getAnOperand(), obj, origin)
}

/* Helper predicates */


private predicate top_level(ControlFlowNode n) {
    n.getScope() instanceof ImportTimeScope and
    /* Only use entry nodes for modules, as exit nodes are implicit uses of all defined variables. */
    not exists(Scope s | s.getAnExitNode() = n)
}

/** Gets the SsaVariable for 'name' at the point of definition of 'cls',
 *  provided that 'name' is used in 'cls'.
 */
private SsaVariable definedAtEntry(Class cls, string name) {
    result = candidateSsa(cls, name) and
    exists(ControlFlowNode entry, ControlFlowNode def | 
        exists(ClassExpr ce | ce.getAFlowNode() = entry and ce.getInnerScope() = cls) and
        result.getDefinition() = def |
        def.getBasicBlock().strictlyDominates(entry.getBasicBlock()) and
        not exists(SsaVariable other | other = candidateSsa(cls, name) |
            def.getBasicBlock().strictlyDominates(other.getDefinition().getBasicBlock())
        )
        or
        exists(BasicBlock b, int i, int j |
            i < j and b.getNode(i) = def and b.getNode(j) = entry and
            not exists(int k | i < k and k < j |
                candidateSsa(cls, name).getDefinition() = b.getNode(k)
            )
        )
    )
}

private SsaVariable candidateSsa(Class cls, string name) {
    exists(Name n | n.getScope() = cls and n.getId() = name) and
    exists(GlobalVariable v | 
        v.getScope() = cls.getScope() and v.getId() = name and
        result.getVariable() = v
    ) 
}

