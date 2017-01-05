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
 * Combined points-to and type-inference for "run-time" (as opposed to "import-time" values)
 * The main relation runtime_points_to(node, object, cls, origin) relates a control flow node
 * to the possible objects it points-to the inferred types of those objects and the 'origin'
 * of those objects. The 'origin' is the point in source code that the object can be traced
 * back to. To handle the case where the class of an object cannot be inferred, but so that
 * we can track the object regardless, a special object "theUnknownType()" is used.
 */
import python

predicate original_values(ControlFlowNode f, Object value) {
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

predicate original_unknowns(ControlFlowNode f) {
    f.getNode() instanceof BinaryExpr
    or
    f.getNode() instanceof UnaryExpr
    or
    f.getNode() instanceof BoolExpr
    or
    f.getNode() instanceof Compare
    or
    f.isParameter()
}

/** INTERNAL -- Use n.refersTo(value, _, origin) instead */
cached predicate base_points_to(ControlFlowNode n, Object value, ControlFlowNode origin) {
    original_values(n, value) and origin = n
    or
    original_unknowns(n) and origin = n and value = n
}

/** Does a call dominates all of the normal exits? 
 * This is a cheap, conservative approximation for "is a method called 
 * unconditionally, given that this function exits normally".
 * The exact version is just too slow.
 */
predicate dominates_all_normal_exits(CallNode call) {
    exists(Function f |
        call.getScope() = f |
        forex(ControlFlowNode exit |
            f.getANormalExit() = exit |
            call.getBasicBlock().dominates(exit.getBasicBlock())
        )
    )
}

/** Whether this variable is not bound. ie. free. */
predicate not_bound(SsaVariable var) {
    not exists(var.getDefinition()) and not exists(var.getAPhiInput())
    or exists(SsaVariable phi | phi = var.getAPhiInput() | not_bound(phi))
}

/** INTERNAL -- Do not use */
ClassObject theUnknownType() {
    py_special_objects(result, "_semmle_unknown_type")
}


/** INTERNAL -- Use m.exportsComplete() instead */
predicate module_exports_complete(Module m) {
    not exists(Call modify, Attribute attr, GlobalVariable all | 
        modify.getScope() = m and modify.getFunc() = attr and 
        all.getId() = "__all__" |
        attr.getObject().(Name).uses(all)
    )
}

/** INTERNAL -- May be modified or deleted without warning. */
predicate is_locally_defined_from_dot_import_in_init(ImportMemberNode f, string name) {
    exists(ImportMember im, ImportExpr module |
        im.getAFlowNode() = f and
        name = im.getName() and
        im.getEnclosingModule().getName().matches("%.\\_\\_init\\_\\_") and
        module = im.getModule()
        |
        module.getLevel() = 1 and
        not exists(module.getName())
        or
        module.getImportedModuleName() = im.getEnclosingModule().getPackage().getName()
    )
}

/** Special case of `from . import name` in an `__init__` module.
 *  In this case the value can be defined in the `__init__` module, 
 *  thus needs to be flow sensitive.
 */
predicate locally_defined_from_dot_import_in_init(ImportMemberNode f, SsaVariable var) {
    is_locally_defined_from_dot_import_in_init(f, var.getId())
    and var.getDefinition().strictlyDominates(f)
}


predicate nonlocal_points_to_candidate(NameNode f) { 
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

predicate call_to_inner_function(Function inner, Function outer) {
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

/** Whether f is a use of a variable and the value of that use must be tf */
predicate must_have_boolean_value(ControlFlowNode f, boolean tf) {
    exists(IsTrue ist | ist.appliesTo(_, f, tf))
}

/** Whether f is a use of a variable and the value of that use must be tf */
predicate must_have_boolean_value_on_edge(ControlledVariable var, BasicBlock pred, BasicBlock succ, boolean tf) {
    exists(IsTrue ist |
        ist.controlsEdge(var, pred, succ, tf)
    )
}

/** The kwargs parameter (**kwargs) in a function definition is always a dict */
predicate kwargs_points_to(ControlFlowNode f, ClassObject cls) {
    exists(Function func | func.getKwarg() = f.getNode()) 
    and
    cls = theDictType()
}

/** The varargs (*varargs) in a function definition is always a tuple */
predicate varargs_points_to(ControlFlowNode f, ClassObject cls) {
    exists(Function func | func.getVararg() = f.getNode()) 
    and
    cls = theTupleType()
}


/** Gets the class of the object for simple cases, namely constants, functions, 
 * comprehensions and built-in objects.
 *
 *  This exists primarily for internal use. Use getAnInferredType() instead.
 */
cached ClassObject simple_types(Object obj) {
    result = comprehension(obj.getOrigin())
    or
    result = collection_literal(obj.getOrigin())
    or
    result = string_literal(obj.getOrigin())
    or
    obj.getOrigin() instanceof CallableExpr and result = thePyFunctionType()
    or
    obj.getOrigin() instanceof Module and result = theModuleType()
    or
    py_cobjecttypes(obj, result)
}

private ClassObject comprehension(Expr e) {
    e instanceof ListComp and result = theListType()
    or
    e instanceof SetComp and result = theSetType()
    or
    e instanceof DictComp and result = theDictType()
    or
    e instanceof GeneratorExp and result = theGeneratorType()
}

private ClassObject collection_literal(Expr e) {
    e instanceof List and result = theListType()
    or
    e instanceof Set and result = theSetType()
    or
    e instanceof Dict and result = theDictType()
    or
    e instanceof Tuple and result = theTupleType()
}

private ClassObject string_literal(Expr e) {
    e instanceof Bytes and result = theBytesType()
    or
    e instanceof Unicode and result = theUnicodeType()
}

private int tuple_index_value(TupleObject t, int i) {
    result = t.getSourceElement(i).getNode().(Num).getN().toInt()
    or
    result = t.getBuiltinElement(i).(NumericObject).intValue()
}

pragma [inline]
int scale_hex_version(int hex) {
    hex >= 50331648 and result = 48 + (hex-50331648)/65536
    or
    hex < 50331648 and result = 32 + (hex-33554432)/65536
}

int version_tuple_value(TupleObject t) {
    not exists(tuple_index_value(t, 1)) and result = tuple_index_value(t, 0)*16
    or
    not exists(tuple_index_value(t, 2)) and result = tuple_index_value(t, 0)*16 + tuple_index_value(t, 1)
    or
    tuple_index_value(t, 2) = 0 and result = tuple_index_value(t, 0)*16 + tuple_index_value(t, 1)
    or
    tuple_index_value(t, 2) > 0 and result = tuple_index_value(t, 0)*16 + tuple_index_value(t, 1) + 1
}

predicate version_compare(Version version, int n, string opname) {
    (n in [32 .. 40] or n in [48 .. 58]) // Versions 2.0 to 2.8 and versions 3.0 to 3.10
    and
    exists(int v |
        version = 2 and v in [32 .. 39]
        or
        version = 3 and v in [48 .. 56]
        |
        v < n and opname = "<"
        or
        v <= n and opname = "<="
        or
        v > n and opname = ">"
        or
        v >= n and opname = ">="
        or
        v = n and opname = "=="
        or
        v != n and opname = "!="
    )
}

class Layer0CustomPointsToFact extends @py_flow_node {

    string toString() { none() }

    predicate pointsTo(Object value, ClassObject cls, ControlFlowNode origin) {
        none()
    }

}

class Layer0PointsToFilter extends ConditionalControlFlowNode {

    Layer0PointsToFilter() {
        none()
    }

    boolean isTrueFor(ControlledVariable var) { none() }

    boolean isTrueForAttribute(SsaVariable var, string attr_name) { none() }

    predicate allowedValue(ControlledVariable var, Object value) { none() }

    predicate allowedClass(ClassObject cls) { none() }

    predicate prohibitedValue(ControlledVariable var, Object value) { none() }

    predicate prohibitedClass(ClassObject cls) { none() }
  
    ControlFlowNode getRelevantUse(ControlledVariable var) { none() }
    
}


predicate baseless_is_new_style(ClassObject cls) {
    cls.isC()
    or
    major_version() >= 3
    or
    exists(cls.declaredMetaClass())
}

/* The following predicates exist in order to provide
 * more precise type information than the underlying
 * database relations. This help to optimise the points-to
 * analysis.
 */

/** Gets the base class of built-in class `cls` */
cached
ClassObject builtin_base_type(ClassObject cls) {
    /* The extractor uses the special name ".super." to indicate the super class of a builtin class */
    py_cmembers(cls, ".super.", result)
}

/** Gets the `name`d attribute of built-in class `cls` */
cached
Object builtin_class_attribute(ClassObject cls, string name) {
    not name = ".super." and
    py_cmembers(cls, name, result)
}

/** Gets the `name`d attribute of built-in module `m` */
cached 
Object builtin_module_attribute(ModuleObject m, string name) {
     py_cmembers(m, name, result)
}

/** Gets the (built-in) class of the built-in object `obj` */
cached
ClassObject builtin_object_type(Object obj) {
    py_cobjecttypes(obj, result)
}

/** Provably extensional names only, to avoid recomputation of 'cached' predicates */
cached 
predicate extensional_name(string n) {
    py_cobjectnames(_, n)
    or
    py_cmembers(_, n, _)
    or
    variable(_, _, n)
    or
    py_strs(n, _, _)
    or
    py_special_objects(_, n)
}


/** Whether this class (not on a super-class) declares name */
cached
predicate class_declares_attribute(ClassObject cls, string name) {
    class_defines_name(cls.getPyClass(), name)
    or
    exists(Object o |
        o = builtin_class_attribute(cls, name) and 
        not exists(ClassObject sup |
            sup = builtin_base_type(cls) and 
            o = builtin_class_attribute(sup, name)
        )
    )
}

/** Whether the class defines name */
private predicate class_defines_name(Class cls, string name) {
    exists(SsaVariable var | name = var.getId() and var.getAUse() = cls.getANormalExit())
}

/** Whether pre precedes post, ignoring the inferred call graph.
 *  That is, is it impossible for post to execute without pre 
 *  having executed at least once, ignoring the inferred call graph.
 */
predicate base_scope_precedes(Scope pre, Scope post, int ranking) {
    not post instanceof ImportTimeScope and pre = post.getEnclosingModule() and ranking = 1
    or
    ranking = 2 and
    exists(Class c |
        pre != post and
        pre.getScope() = c and post.getScope() = c and
        not exists(post.(Function).getADecorator()) |
        pre.getName() = "__init__" or pre.getName() = "new" 
    )
}

/** Gets a return value CFG node, provided that is safe to track across returns */
ControlFlowNode safe_return_node(PyFunctionObject func) {
    result = func.getAReturnedNode()
    // Not a parameter
    and not exists(Parameter p, SsaVariable pvar |
        p.asName().getAFlowNode() = pvar.getDefinition() and
        result = pvar.getAUse()
    ) and
    // No alternatives
    result.strictlyDominates(func.getFunction().getReturnNode())
}

predicate is_parameter_default(ControlFlowNode def) {
   exists(Parameter p | p.getDefault().getAFlowNode() = def)
}

predicate base_defined_in_scope(GlobalVariable g, Scope s) {
    g.getAStore().getScope() = s
}

pragma [noinline]
predicate base_at_scope_exit(Scope s, string name, SsaVariable var) {
    var.getVariable() instanceof GlobalVariable and
    var.getAUse() = s.getANormalExit() and
    var.getId() = name
}

/** Mark simple cases to avoid unneccessary computation */
DefinitionNode simple_global_defn(GlobalVariable g) {
   result = g.getAStore().getAFlowNode()
   and
   strictcount(g.getAStore().getAFlowNode()) = 1
   and
   not exists(builtin_object(g.getId()))
   and
   not exists(NameNode n | n.uses(g) and n.getScope() instanceof Class)
}

predicate indexed_callsite_for_class(Class cls, BasicBlock b, int i) {
    exists(ClassDef cdef |
        cdef.getDefinedClass() = cls and
        b.getNode(i) = cdef.getValue().getAFlowNode()
    )
}


/** INTERNAL -- Do not use */
predicate last_simple_attribute_store_in_scope(SsaVariable var, string name, ControlFlowNode stored) {
    extensional_name(name) and
    exists(AttrNode fstore |
        fstore.(DefinitionNode).getValue() = stored |
        fstore.isStore() and
        var.getAUse() = fstore.getObject(name)
        and not exists(AttrNode better |
            better.isStore() and
            var.getAUse() = better.getObject(name) and
            fstore.strictlyDominates(better)
        )
    )
}
