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

/** Provides classes and predicates for determining the uses and definitions of 
 * variables for ESSA form.
 */

import python
private import semmle.python.pointsto.Base

private predicate variable_or_attribute_defined_out_of_scope(Variable v) {
    exists(NameNode n | n.defines(v) and not n.getScope() = v.getScope())
    or
    exists(AttrNode a | a.isStore() and a.getObject() = v.getAUse() and not a.getScope() = v.getScope())
}

/** Holds if the global variable `v` may be used in the call `call`. */
private predicate global_variable_maybe_used_in_call(GlobalVariable v, CallNode call) {
    exists(Module m |
        m = call.getScope() and v.getScope() = m and
        v.getAStore().getScope() = m and
        v.getALoad().getScope() != m
    )
}

private predicate class_with_global_metaclass(Class cls, GlobalVariable metaclass) {
    metaclass.getId() = "__metaclass__" and major_version() = 2 and
    cls.getEnclosingModule() = metaclass.getScope()
}

/** Python specific version of `SsaSourceVariable`. */
private class PythonSsaSourceVariable extends SsaSourceVariable {

    PythonSsaSourceVariable() {
        /* Exclude `True`, `False` and `None` */
        not this.(Variable).getALoad() instanceof NameConstant
    }

    string getName() {
        result = this.(Variable).getId()
    }

    override ControlFlowNode getAUse() {
        result = this.getASourceUse()
        or
        result = this.implicitUseAtScopeExit()
        or
        global_variable_maybe_used_in_call(this, result)
        or
        result.getScope() = this.(Variable).getScope() and
        import_from_dot_in_init(result.(ImportMemberNode).getModule(this.getName()))
        or
        exists(ImportTimeScope scope |
            scope.entryEdge(result, _) |
            this = scope.getOuterVariable(_) or
            this.(Variable).getAUse().getScope() = scope
        )
        or
        /* `import *` is a definition of *all* variables, so must be a use as well, for pass-through
         * once we have established that a variable is not redefined.
         */
        SsaSource::import_star_refinement(this, result, _)
        or
        SsaSource::variable_refined_at_callsite(this, result)
        or
        /* For implicit use of __metaclass__ when constructing class */
        exists(Class c |
            class_with_global_metaclass(c, this) and
            c.(ImportTimeScope).entryEdge(result, _)
        )
    }

    private ControlFlowNode implicitUseAtScopeExit() {
        exists(Scope s |
            result = s.getANormalExit() |
            exists(NameNode n | n.defines(this) and n.getScope() = s)
            or
            variable_or_attribute_defined_out_of_scope(this) and
            s.getScope*() = this.(Variable).getScope()
            or
            this.(Variable).isSelf() and s = this.(Variable).getScope()
            or
            (s instanceof Module or s.(Function).isInitMethod()) and
            exists(NameNode n | n.defines(this) and n.getScope() = s) and
            s.getScope*() = this.(Variable).getScope()
            or
            s instanceof Module and this.(Variable).getScope() = s and
            (this.getName() = "__name__" or this.getName() = "__package__")
            or
            class_with_global_metaclass(s, this)
        )
        or
        exists(ImportTimeScope s |
            result = s.getANormalExit() and this.(Variable).getScope() = s and
            implicit_definition(this)
        )
    }

    override predicate hasDefiningNode(ControlFlowNode def) {
        SsaSource::scope_entry_definition(this, def)
        or
        SsaSource::assignment_definition(this, def, _)
        or
        SsaSource::multi_assignment_definition(this, def)
        or
        SsaSource::deletion_definition(this, def)
        or
        SsaSource::iteration_defined_variable(this, def)
        or
        SsaSource::init_module_submodule_defn(this, def)
        or
        SsaSource::module_name_defn(this, def, _)
        or
        SsaSource::parameter_definition(this, def)
        or
        SsaSource::nonlocal_variable_entry_definition(this, def)
        or
        SsaSource::exception_capture(this, def)
        or
        SsaSource::with_definition(this, def)
    }

    override predicate hasDefiningEdge(BasicBlock pred, BasicBlock succ) {
        none()
    }

    override predicate hasRefinement(ControlFlowNode use, ControlFlowNode def) {
        refinement(this, use, def)
    }

    override predicate hasRefinementEdge(ControlFlowNode use, BasicBlock pred, BasicBlock succ) {
        use.(NameNode).uses(this) and
        exists(ControlFlowNode test |
            test.getAChild*() = use and
            test.isBranch() and
            test = pred.getLastNode()
        ) and
        (pred.getAFalseSuccessor() = succ or pred.getATrueSuccessor() = succ)
        and
        /* There is a store to this variable -- We don't want to refine builtins */
        exists(this.(Variable).getAStore()) and
        /* There is at least one use or definition of the variable that is controlled by the test */
        exists(ControlFlowNode n |
            n = this.getAUse() or
            this.hasDefiningNode(n) |
            pred.(ConditionBlock).controls(n.getBasicBlock(), _)
        )
    }

    override ControlFlowNode getASourceUse() {
        result.(NameNode).uses(this)
        or
        result.(NameNode).deletes(this)
    }

}

/** Holds if this variable is implicitly defined */
private predicate implicit_definition(Variable v) {
    v.getId() = "*"
    or
    exists(ImportStar is | is.getScope() = v.getScope())
}

cached module SsaSource {

    /** Holds if `v` is used as the receiver in a method call. */
    cached predicate method_call_refinement(Variable v, ControlFlowNode use, CallNode call) {
        use = v.getAUse() and 
        call.getFunction().(AttrNode).getObject() = use
    }

    /** Holds if `v` is defined by assignment at `defn` and given `value`. */
    cached predicate assignment_definition(Variable v, ControlFlowNode defn, ControlFlowNode value) {
        defn.(NameNode).defines(v) and defn.(DefinitionNode).getValue() = value
    }

    /** Holds if `v` is defined by assignment of the captured exception. */
    cached predicate exception_capture(Variable v, NameNode defn) {
        defn.defines(v) and
        exists(ExceptFlowNode ex | ex.getName() = defn)
    }

    /** Holds if `v` is defined by a with statement. */
    cached predicate with_definition(Variable v, ControlFlowNode defn) {
        exists(With with, Name var | 
            with.getOptionalVars() = var and
            var.getAFlowNode() = defn |
            var = v.getAStore()
        )
    }

    /** Holds if `v` is defined by multiple assignment at `defn`. */
    cached predicate multi_assignment_definition(Variable v, ControlFlowNode defn) {
        defn.(NameNode).defines(v) and 
        not exists(defn.(DefinitionNode).getValue()) and
        exists(TupleNode t | t.getAnElement() = defn)
    }

    /** Holds if `v` is defined outside its scope and thus *may* be redefined by `call`. */
    cached predicate variable_refined_at_callsite(Variable v, CallNode call) {
        not v.isSelf() and
        variable_or_attribute_defined_out_of_scope(v) and
        call.getScope().getScope*() = v.getScope()
    }

    /** Holds if `v` is a non-local to the scope which has `entry` as its entry node */
    cached predicate nonlocal_variable_entry_definition(LocalVariable v, ControlFlowNode entry) {
        exists(Function f |
            f.getEntryNode() = entry |
            v.getALoad().getScope() = f and
            not v.getScope() = f
        )
    }

    /** Holds if `v` is defined externally to the scope, but is usable within the scope */
    cached predicate scope_entry_definition(Variable v, ControlFlowNode entry) {
        not v.getId() = "*" and
        not init_module_submodule_defn(v, entry) and
        not module_name_defn(v, entry, _) and
        not v.isParameter() and
        exists(Scope s |
            s.getEntryNode() = entry |
            /* Variable belongs to same scope as entry */
            v.getScope() = s
            or
            /* Variable is global to module enclosing scope and is modified in an inner scope */
            exists(NameNode def | def.defines(v) and def.getScope() != v.getScope()) and
            s.getEnclosingModule() = v.getScope()
            or
            /* Variable is global, defined (so it isn't just a builtin), and used in scope */
            v instanceof GlobalVariable and exists(NameNode def | def.defines(v)) and
            exists(NameNode use | use.uses(v) and use.getScope() = s)
            or
            /* If a variable is refined, then it must exist */
            exists(ControlFlowNode use |
                refinement(v, use, _) and
                use.getScope().getEntryNode() = entry
            )
            or
            /* For implicit use of __metaclass__ when constructing class */
            class_with_global_metaclass(s, v)
        )
    }

    /** Holds if `v` is defined by a `for` statement, the definition being `defn` */
    cached predicate iteration_defined_variable(Variable v, ControlFlowNode defn) {
        exists(For f | f.getTarget() = defn.getNode()) and
        defn.(NameNode).defines(v)
    }

    /** Holds if `v` is a parameter variable and `defn` is the CFG node for that parameter. */
    cached predicate parameter_definition(Variable v, ControlFlowNode defn) {
        exists(Function f, Name param |
            f.getAnArg() = param or
            f.getVararg() = param or
            f.getKwarg() = param or
            f.getKeywordOnlyArg(_) = param |
            defn.getNode() = param and
            param.getVariable() = v
        )
    }

    /** Holds if `v` is deleted at `del`. */
    cached predicate deletion_definition(Variable v, DeletionNode del) {
        del.getTarget().(NameNode).deletes(v)
    }

    /** Holds if the name of `var` refers to a submodule of a package and `f` is the entry point
     * to the __init__ module of that package.
     */
    cached predicate init_module_submodule_defn(Variable var, ControlFlowNode f) {
        exists(Module init |
            init.isPackageInit() and exists(init.getPackage().getSubModule(var.getId())) and
            var instanceof GlobalVariable and init.getEntryNode() = f and
            var.getScope() = init
        )
    }

    /** Holds if the name of `var` is __name__ and `f` is the entry point to the module named `module_name`. */
    cached predicate module_name_defn(Variable var, ControlFlowNode f, string module_name) {
        exists(Module m |
            m.getEntryNode() = f and
            var.getScope() = m and
            var.getId() = "__name__" |
            if m.isPackageInit() then
                module_name = m.getPackage().getName()
            else
                module_name = m.getName()
        )
    }

    /** Holds if the `v` is in scope at a `from import ... *` and may thus be redefined by that statement */
    cached predicate import_star_refinement(Variable v, ControlFlowNode use, ControlFlowNode def) {
        use = def and def instanceof ImportStarNode
        and
        (
            v.getScope() = def.getScope()
            or
            exists(NameNode other |
                other.uses(v) and
                def.getScope() = other.getScope()
            )
        )
    }

    /** Holds if an attribute is assigned at `def` and `use` is the use of `v` for that assignment */
    cached predicate attribute_assignment_refinement(Variable v, ControlFlowNode use, ControlFlowNode def) {
        use.(NameNode).uses(v) and
        def.isStore() and def.(AttrNode).getObject() = use
    }

    /** Holds if a `v` is used as an argument to `call`, which *may* modify the object referred to by `v` */
    cached predicate argument_refinement(Variable v, ControlFlowNode use, CallNode call) {
        use.(NameNode).uses(v) and
        call.getArg(0) = use and
        not method_call_refinement(v, _, call) and
        not variable_refined_at_callsite(v, call) and
        not test_refinement(v, _, call)
    }

    /** Holds if an attribute is deleted  at `def` and `use` is the use of `v` for that deletion */
    cached predicate attribute_deletion_refinement(Variable v, NameNode use, DeletionNode def) {
        use.uses(v) and
        def.getTarget().(AttrNode).getObject() = use
    }

    /** Holds if the set of possible values for `v` is refined by `test` and `use` is the use of `v` in that test. */
    cached predicate test_refinement(Variable v, ControlFlowNode use, ControlFlowNode test) {
        use.(NameNode).uses(v) and
        test.getAChild*() = use and
        test.isBranch() and
        not exists(ControlFlowNode parent | parent.getAChild() = test and parent.isBranch()) and
        not exists(BasicBlock b | b.getLastNode() = test)
    }

}

private predicate refinement(Variable v, ControlFlowNode use, ControlFlowNode def) {
    SsaSource::import_star_refinement(v, use, def)
    or
    SsaSource::attribute_assignment_refinement(v, use, def)
    or
    SsaSource::argument_refinement(v, use, def)
    or
    SsaSource::attribute_deletion_refinement(v, use, def)
    or
    SsaSource::test_refinement(v, use, def)
    or
    SsaSource::method_call_refinement(v, use, def)
    or
    SsaSource::variable_refined_at_callsite(v, def) and def = use
}
