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
 * Definition tracking for jump-to-defn query
 */
 import python

import semmle.dataflow.SSA
import semmle.python.pointsto.Final

private newtype TDefinition =
    TLocalDefinition(AstNode a) {
        a instanceof Expr or a instanceof Stmt
    }
    or
    TRemoteDefinition(Symbol s)

private newtype TSymbol =
    TModule(Module m)
    or
    TMember(Symbol outer, string part) {
        exists(Object o |
            outer.resolvesTo() = o |
            o.(ModuleObject).hasAttribute(part)
            or
            o.(ClassObject).hasAttribute(part)
        )
    }

/** A "symbol" referencing an object in another module
 * Symbols are represented by the module name and the dotted name by which the 
 * object would be referred to in that module.
 * For example for the code:
 * ```
 * class C:
 *     def m(self): pass
 * ```
 * If the code were in a module `mod`, 
 * then symbol for the method `m` would be "mod/C.m"
 */
class Symbol extends TSymbol {

    string toString() {
        exists(Module m |
            this = TModule(m) and result = m.getName()
        )
        or 
        exists(TModule outer, string part |
            this = TMember(outer, part) and
            outer = TModule(_) and
            result = outer.(Symbol).toString() + "/" + part
        )
        or 
        exists(TMember outer, string part |
            this = TMember(outer, part) and
            outer = TMember(_, _) and
            result = outer.(Symbol).toString() + "." + part
        )
    }

    AstNode find() {
        this = TModule(result)
        or
        exists(Symbol s, string name |
            this = TMember(s, name) |
            exists(ClassObject cls |
                s.resolvesTo() = cls and
                cls.attributeRefersTo(name, _, result.getAFlowNode())
            )
            or
            exists(ModuleObject m |
                s.resolvesTo() = m and
                m.attributeRefersTo(name, _, result.getAFlowNode())
            )
        )
    }

    Object resolvesTo() {
        this = TModule(result.(ModuleObject).getModule())
        or
        exists(Symbol s, string name, Object o |
            this = TMember(s, name) and 
            o = s.resolvesTo() and
            result = attribute_in_scope(o, name)
        )
    }

    Module getModule() {
        this = TModule(result)
        or
        exists(Symbol outer |
            this = TMember(outer, _) and result = outer.getModule()
        )
    }

    Symbol getMember(string name) {
        result = TMember(this, name)
    }

}

/* Helper for Symbol.resolvesTo() */
private Object attribute_in_scope(Object obj, string name) {
    exists(ClassObject cls |
        cls = obj |
        cls.lookupAttribute(name) = result and result.(ControlFlowNode).getScope() = cls.getPyClass()
    )
    or
    exists(ModuleObject mod |
        mod = obj |
        mod.getAttribute(name) = result and result.(ControlFlowNode).getScope() = mod.getModule()
        and not result.(ControlFlowNode).isEntryNode()
    )
}


/** A definition for the purposes of jump-to-definition
 */
class Definition extends TDefinition {

    abstract string toString();

    abstract Module getModule();

    abstract Location getLocation();

}

/** A "remote" definition, meaning that it is not in the same module.
 */
class RemoteDefinition extends Definition, TRemoteDefinition {

    string toString() {
        result = "Remote definition " + this.getSymbol().toString()
    }

    Symbol getSymbol() {
        this = TRemoteDefinition(result)
    }

    predicate interProject() {
        exists(Module m |
            m = this.getModule() and
            not exists(m.getFile().getRelativePath())
        )
    }

    Module getModule() {
        exists(Symbol s |
            this = TRemoteDefinition(s) and
            result = s.getModule()
        )
    }

    Definition getMember(string name) {
        result = TRemoteDefinition(this.getSymbol().getMember(name))
    }

    Location getLocation() {
        result = this.getSymbol().find().getLocation()
    }

    AstNode find() {
        result = this.getSymbol().find()
    }

}

/** A "local" definition, meaning that it is in the same module.
 */
class LocalDefinition extends Definition, TLocalDefinition {


    string toString() {
        result = "Local definition " + this.getAstNode().getLocation().toString()
    }

    AstNode getAstNode() {
        this = TLocalDefinition(result)
    }

    Module getModule() {
        result = this.getAstNode().getScope().getEnclosingModule()
    }

    Location getLocation() {
        result = this.getAstNode().getLocation()
    }

}

private predicate jump_to_defn(ControlFlowNode use, Definition defn) {
    exists(EssaVariable var |
        use = var.getASourceUse() and
        ssa_variable_defn(var, defn)
    )
    or
    exists(string name |
        use.isLoad() and
        jump_to_defn_attribute(use.(AttrNode).getObject(name), name, defn)
    )
    or
    exists(ImportExprNode imp, PythonModuleObject mod |
        imp = use and imp.refersTo(mod) and
        defn = TRemoteDefinition(TModule(mod.getModule()))
    )
    or
    exists(ImportMemberNode imp, PythonModuleObject mod, string name |
        imp = use and imp.getModule(name).refersTo(mod) and
        defn = TRemoteDefinition(TMember(TModule(mod.getModule()), name))
    )
    or
    (use instanceof PyFunctionObject or use instanceof ClassObject) and
    defn.(RemoteDefinition).find() = use.getNode()

}

/* Prefer local definitions to remote ones */
private predicate preferred_jump_to_defn(Expr use, Definition def) {
    not use instanceof ClassExpr and
    not use instanceof FunctionExpr and
    jump_to_defn(use.getAFlowNode(), def) and
    (
        def instanceof LocalDefinition
        or
        not exists(LocalDefinition other | jump_to_defn(use.getAFlowNode(), other))
    )
}

private predicate unique_jump_to_defn(Expr use, Definition def) {
    preferred_jump_to_defn(use, def) and
    not exists(Definition other |
        other != def and
        preferred_jump_to_defn(use, other)
    )
}

private predicate ssa_variable_defn(EssaVariable var, Definition defn) {
    ssa_defn_defn(var.getDefinition(), defn)
}

/** Holds if the phi-function `phi` refers to (`value`, `cls`, `origin`) given the context `context`. */
private predicate ssa_phi_defn(PhiFunction phi, Definition defn) {
    ssa_variable_defn(phi.getAnInput(), defn)
}

/** Holds if the ESSA defn `def`  refers to (`value`, `cls`, `origin`) given the context `context`. */
private predicate ssa_defn_defn(EssaDefinition def, Definition defn) {
    ssa_phi_defn(def, defn)
    or
    ssa_node_defn(def, defn)
    or
    ssa_filter_defn(def, defn)
    or
    ssa_node_refinement_defn(def, defn)
}

/** Holds if ESSA edge refinement, `def`, is defined by `defn` */
predicate ssa_filter_defn(PyEdgeRefinement def, Definition defn) {
    ssa_variable_defn(def.getInput(), defn)
}

/** Holds if ESSA defn, `uniphi`,is defined by `defn` */
predicate uni_edged_phi_defn(SingleSuccessorGuard uniphi, Definition defn) {
    ssa_variable_defn(uniphi.getInput(), defn)
}

pragma [noinline]
private predicate ssa_node_defn(EssaNodeDefinition def, Definition defn) {
    assignment_jump_to_defn(def, defn)
    or
    parameter_defn(def, defn)
    or
    delete_defn(def, defn)
    or
    scope_entry_defn(def, defn)
    or
    implicit_submodule_defn(def, defn)
}

/* Definition for normal assignments `def = ...` */
private predicate assignment_jump_to_defn(AssignmentDefinition def, Definition defn) {
    defn = TLocalDefinition(def.getValue().getNode())
    or
    defn = TRemoteDefinition(_) and jump_to_defn(def.getValue(), defn)
}

pragma [noinline]
private predicate ssa_node_refinement_defn(EssaNodeRefinement def, Definition defn) {
    method_callsite_defn(def, defn)
    or
    import_star_defn(def, defn)
    or
    attribute_assignment_defn(def, defn)
    or
    callsite_defn(def, defn)
    or
    argument_defn(def, defn)
    or
    attribute_delete_defn(def, defn)
    or
    uni_edged_phi_defn(def, defn)
}


/* Definition for parameter. `def foo(param): ...` */
private predicate parameter_defn(ParameterDefinition def, LocalDefinition defn) {
    defn.getAstNode() = def.getDefiningNode().getNode()
}

/* Definition for deletion: `del name` */
private predicate delete_defn(DeletionDefinition def, Definition defn) {
    none()
}

/* Implicit "defn" of the names of submodules at the start of an `__init__.py` file.
 */
private predicate implicit_submodule_defn(ImplicitSubModuleDefinition def, Definition defn) {

    exists(PackageObject package, ModuleObject mod |
        package.getInitModule().getModule() = def.getDefiningNode().getScope() and
        mod = package.submodule(def.getSourceVariable().getName()) and
        defn = TRemoteDefinition(TModule(mod.getModule()))
    )

}

/* Helper for scope_entry_value_transfer(...). Transfer of values from the callsite to the callee, for enclosing variables, but not arguments/parameters */
private predicate scope_entry_value_transfer_at_callsite(EssaVariable pred_var, ScopeEntryDefinition succ_def) {
    exists(CallNode callsite, FunctionObject f |
        f.getACall() = callsite and
        pred_var.getSourceVariable() = succ_def.getSourceVariable() and
        pred_var.getAUse() = callsite and
        succ_def.getDefiningNode() = f.getFunction().getEntryNode()
    )
}

/* Model the transfer of values at scope-entry points. Transfer from `pred_var, pred_context` to `succ_def, succ_context` */
private
predicate scope_entry_value_transfer(EssaVariable pred_var, ScopeEntryDefinition succ_def) {
    BaseFlow::scope_entry_value_transfer_from_earlier(pred_var, _, succ_def, _)
    or
    scope_entry_value_transfer_at_callsite(pred_var, succ_def)
    or
    class_entry_value_transfer(pred_var, succ_def)
}

/* Helper for scope_entry_value_transfer */
private
predicate class_entry_value_transfer(EssaVariable pred_var, ScopeEntryDefinition succ_def) {
    exists(ImportTimeScope scope, ControlFlowNode class_def |
        class_def = pred_var.getAUse() and
        scope.entryEdge(class_def, succ_def.getDefiningNode()) and
        pred_var.getSourceVariable() = succ_def.getSourceVariable()
    )
}

/* Definition for implicit variable declarations at scope-entry. */
pragma [noinline]
private predicate scope_entry_defn(ScopeEntryDefinition def, Definition defn) {
    /* Transfer from another scope */
    exists(EssaVariable var |
        scope_entry_value_transfer(var, def) and
        ssa_variable_defn(var, defn)
    )
}

/* Definition for a variable (possibly) redefined by a call:
 * Just assume that call does not define variable
 */
pragma [noinline]
private predicate callsite_defn(CallsiteRefinement def, Definition defn) {
    ssa_variable_defn(def.getInput(), defn)
}

/* Pass through for `self` for the implicit re-defn of `self` in `self.foo()` */
private predicate method_callsite_defn(MethodCallsiteRefinement def, Definition defn) {
    /* The value of self remains the same, only the attributes may change */
    ssa_variable_defn(def.getInput(), defn)
}

/** Helpers for import_star_defn */
pragma [noinline]
private predicate module_and_name_for_import_star(ModuleObject mod, string name, ImportStarRefinement def) {
    exists(ImportStarNode im_star |
        im_star = def.getDefiningNode() |
        name = def.getSourceVariable().getName() and
        im_star.getModule().refersTo(mod) and
        mod.exports(name)
    )
}

/** Holds if `def` is technically a defn of `var`, but the `from ... import *` does not in fact define `var` */
pragma [noinline]
private predicate variable_not_redefined_by_import_star(EssaVariable var, ImportStarRefinement def) {
    var = def.getInput() and
    exists(ModuleObject mod |
        def.getDefiningNode().(ImportStarNode).getModule().refersTo(mod) and
        not mod.exports(var.getSourceVariable().getName())
    )
}

/* Definition for `from ... import *` */
private predicate import_star_defn(ImportStarRefinement def, Definition defn) {
    exists(ModuleObject mod, string name |
        module_and_name_for_import_star(mod, name, def) |
        /* Attribute from imported module */
        defn = TRemoteDefinition(TMember(TModule(mod.getModule()), name))
    )
    or
    exists(EssaVariable var |
        /* Retain value held before import */
        variable_not_redefined_by_import_star(var, def) and
        ssa_variable_defn(var, defn)
    )
}

/** Attribute assignments have no effect as far as defn tracking is concerned */
private predicate attribute_assignment_defn(AttributeAssignment def, Definition defn) {
    ssa_variable_defn(def.getInput(), defn)
}

/** Ignore the effects of calls on their arguments. This is an approximation, but attempting to improve accuracy would be very expensive for very little gain. */
private predicate argument_defn(ArgumentRefinement def, Definition defn) {
    ssa_variable_defn(def.getInput(), defn)
}

/** Attribute deletions have no effect as far as value tracking is concerned. */
pragma [noinline]
private predicate attribute_delete_defn(EssaAttributeDeletion def, Definition defn) {
    ssa_variable_defn(def.getInput(), defn)
}

/* Definition flow for attributes. These mirror the "normal" defn predicates.
 * For each defn predicate `xxx_defn(XXX def, Definition defn)`
 * There is an equivalent predicate that tracks the values in attributes:
 * `xxx_jump_to_defn_attribute(XXX def, string name, Definition defn)`
 *  */

/** INTERNAL -- Public for testing only.
 * Holds if the attribute `name` of the ssa variable `var` refers to (`value`, `cls`, `origin`)
 */
predicate ssa_variable_jump_to_defn_attribute(EssaVariable var, string name, Definition defn) {
    ssa_defn_jump_to_defn_attribute(var.getDefinition(), name, defn)
}

/** Helper for ssa_variable_jump_to_defn_attribute */
private predicate ssa_defn_jump_to_defn_attribute(EssaDefinition def, string name, Definition defn) {
    ssa_phi_jump_to_defn_attribute(def, name, defn)
    or
    ssa_node_jump_to_defn_attribute(def, name, defn)
    or
    ssa_node_refinement_jump_to_defn_attribute(def, name, defn)
    or
    ssa_filter_jump_to_defn_attribute(def, name, defn)
}

/** Holds if ESSA edge refinement, `def`, is defined by `defn` of `priority` */
predicate ssa_filter_jump_to_defn_attribute(PyEdgeRefinement def, string name, Definition defn) {
    ssa_variable_jump_to_defn_attribute(def.getInput(), name, defn)
}

/** Holds if the attribute `name` of the ssa phi-function defn `phi` refers to (`value`, `cls`, `origin`) */
private predicate ssa_phi_jump_to_defn_attribute(PhiFunction phi, string name, Definition defn) {
    ssa_variable_jump_to_defn_attribute(phi.getAnInput(), name, defn)
}

/** Helper for ssa_defn_jump_to_defn_attribute */
pragma[noinline]
private predicate ssa_node_jump_to_defn_attribute(EssaNodeDefinition def, string name, Definition defn) {
    assignment_jump_to_defn_attribute(def, name, defn)
    or
    self_parameter_jump_to_defn_attribute(def, name, defn)
    or
    scope_entry_jump_to_defn_attribute(def, name, defn)
}

/** Helper for ssa_defn_jump_to_defn_attribute */
pragma[noinline]
private predicate ssa_node_refinement_jump_to_defn_attribute(EssaNodeRefinement def, string name, Definition defn) {
    attribute_assignment_jump_to_defn_attribute(def, name, defn)
    or
    argument_jump_to_defn_attribute(def, name, defn)
}

pragma[noinline]
private predicate scope_entry_jump_to_defn_attribute(ScopeEntryDefinition def, string name, Definition defn) {
    exists(EssaVariable var |
        scope_entry_value_transfer(var, def) and
        ssa_variable_jump_to_defn_attribute(var, name, defn)
    )
}


private predicate jump_to_defn_attribute(ControlFlowNode use, string name, Definition defn) {
    /* Local attribute */
    exists(EssaVariable var |
        use = var.getASourceUse() and
        ssa_variable_jump_to_defn_attribute(var, name, defn)
    )
    or
    exists(RemoteDefinition usedef |
        jump_to_defn(use, usedef) and
        defn = usedef.getMember(name)
    )
    or
    /* Instance attributes */
    exists(ClassObject cls |
        cls != theSuperType() and
        use.refersTo(_, cls, _) and
        exists(RemoteDefinition r |
            defn = r.getMember(name) and
            r.getSymbol().resolvesTo() = cls
        )
    )
    or
    /* Super attributes */
    exists(AttrNode f, Object function |
        use = f.getObject(name) and
        FinalPointsTo::super_bound_method(f, _, _, function) and
        function = defn.(RemoteDefinition).getSymbol().resolvesTo()
    )
}

pragma[noinline]
private predicate assignment_jump_to_defn_attribute(AssignmentDefinition def, string name, Definition defn) {
    jump_to_defn_attribute(def.getValue(), name, defn)
}

pragma[noinline]
private predicate attribute_assignment_jump_to_defn_attribute(AttributeAssignment def, string name, Definition defn) {
    defn.(LocalDefinition).getAstNode() = def.getDefiningNode().getNode() and name = def.getName()
    or
    ssa_variable_jump_to_defn_attribute(def.getInput(), name, defn) and not name = def.getName()
}

/** Holds if `def` defines the attribute `name`
 * `def` takes the form `setattr(use, "name")` where `use` is the input to the defn.
 */
private predicate sets_attribute(ArgumentRefinement def, string name) {
    exists(CallNode call |
        call = def.getDefiningNode() and
        call.getFunction().refersTo(builtin_object("setattr")) and
        def.getInput().getAUse() = call.getArg(0) and
        call.getArg(1).getNode().(StrConst).getText() = name
    )
}

pragma[noinline]
private predicate argument_jump_to_defn_attribute(ArgumentRefinement def, string name, Definition defn) {
    if sets_attribute(def, name) then
        jump_to_defn(def.getDefiningNode().(CallNode).getArg(2), defn)
    else
        ssa_variable_jump_to_defn_attribute(def.getInput(), name, defn)
}

/** Gets the (temporally) preceding variable for "self", e.g. `def` is in method foo() and `result` is in `__init__()`.  */
private EssaVariable preceding_self_variable(ParameterDefinition def) {
    exists(Function preceding, Function method |
        method = def.getScope() and 
        // Only methods
        preceding.isMethod() and preceding.precedes(method) and
        result.reachesExit() and result.getSourceVariable().(Variable).isSelf() and
        result.getScope() = preceding
    )
}

pragma [noinline]
private predicate self_parameter_jump_to_defn_attribute(ParameterDefinition def, string name, Definition defn) {
    ssa_variable_jump_to_defn_attribute(preceding_self_variable(def), name, defn)
    or
    exists(FunctionObject meth, CallNode call, ControlFlowNode obj |
        meth.getFunction() = def.getScope() and
        meth.getAMethodCall() = call and
        call.getFunction().(AttrNode).getObject() = obj and
        jump_to_defn_attribute(obj, name, defn)
    )
}

/** Gets a definition for 'use'.
 * This exists primarily for testing use `getPreferredDefinition()` instead.
 */
Definition getADefinition(Expr use) {
    jump_to_defn(use.getAFlowNode(), result) and
    not use instanceof Call and
    not use.isArtificial() and
    // Not the use itself
    not result = TLocalDefinition(use)
}

/** Gets the unique definition for 'use', if one can be found.
 * Helper for the jump-to-definition query.
 */
Definition getUniqueDefinition(Expr use) {
    unique_jump_to_defn(use, result) and
    not use instanceof Call and
    not use.isArtificial() and
    // Not the use itself
    not result = TLocalDefinition(use)
}


/** Helper class to get suitable locations for attributes */
class NiceLocationExpr extends @py_expr {

    string toString() {
        result = this.(Expr).toString()
    }

    predicate hasLocationInfo(string f, int bl, int bc, int el, int ec) {
        /* Attribute location for x.y is that of 'y' so that url does not overlap with that of 'x' */ 
        exists(int abl, int abc |
            this.(Attribute).getLocation().hasLocationInfo(f, abl, abc, el, ec) |
            bl = el and bc = ec - this.(Attribute).getName().length() + 1
        )
        or
        this.(Name).getLocation().hasLocationInfo(f, bl, bc, el, ec)
        or
        /* Show xxx in `from xxx import y` */
        exists(ImportMember im | im.getModule() = this) and
        this.(ImportExpr).getLocation().hasLocationInfo(f, bl, bc, el, ec)
    }

}


