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

/** Utilities for jump to definition query */

import python

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


private predicate self_attribute_defn(ClassObject cls, string name, SelfAttributeStore defn) {
    defn.getScope() = cls.getAnImproperSuperType().getPyClass().getInitMethod()
    and
    defn.getName() = name
}


private predicate overriding_descriptor(ClassObject cls, string name, AstNode defn) {
    exists(Object obj |
        cls.attributeRefersTo(name, obj, defn.getAFlowNode()) |
        obj.getAnInferredType().isOverridingDescriptorType()
    )
}

/* Find the definition of an attribute of 'self', respecting descriptors, 
 * but ignoring overrides of __getattribute__ or __getattr__.
 */
private predicate self_attr_defn(SelfAttributeRead attr, AstNode defn) {
    exists(ClassObject cls |
        attr.getClass() = cls.getPyClass() |
        /* Overriding descriptors take precedence */
        overriding_descriptor(cls, attr.getName(), defn)
        or
        /* If no overriding descriptor is present, then look for an instance attribute */
        not overriding_descriptor(cls, attr.getName(), _) and
        self_attribute_defn(cls, attr.getName(), defn) and
        strictcount(AstNode a | self_attribute_defn(cls, attr.getName(), a)) = 1
        or
        /* Otherwise fall back on a non-overriding descriptor (if any). */
        not overriding_descriptor(cls, attr.getName(), _) and
        not self_attribute_defn(cls, attr.getName(), _) and
        cls.attributeRefersTo(attr.getName(), _, defn.getAFlowNode())
    )
}

/* Find the definition of an attribute other than 'self', ignoring instance attributes */
private predicate instance_attr_defn(Attribute attr, AstNode defn) {
    not attr instanceof SelfAttribute and 
    attr.getCtx() instanceof Load and
    exists(ClassObject cls |
        attr.getAFlowNode().(AttrNode).getObject().refersTo(_, cls, _) and
        cls.attributeRefersTo(attr.getName(), _, defn.getAFlowNode())
    )
}

private predicate inferred_definition(Expr use, AstNode defn) {
    not use = defn and
    exists(AstNode value | 
        use.refersTo(_, value) and
        not use.(Name).getCtx() instanceof Store
        |
        /* value is lhs of assignment, use rhs as definition */
        exists(AssignStmt a |
            /* If more than one target (a = b = c) we end up with a defining b and vice versa */
            strictcount(a.getATarget()) = 1 and
            a.getValue() = value and 
            defn = a.getATarget()
        )
        or
        /* Non assignment */
        not exists(AssignStmt a |
            strictcount(a.getATarget()) = 1 and a.getValue() = value
        ) and defn = value
        or
        /* Get underlying function/class from decorator call */
        defn.(ClassExpr).getADecoratorCall() = value
        or
        defn.(FunctionExpr).getADecoratorCall() = value
    )
}

private predicate local_definition(Expr use, AstNode defn) {
    exists(SsaVariable var |
        var.getAUse().getNode() = use and
        var.getDefinition().getNode() = defn and
        not exists(var.getAPhiInput())
    )
}

/** Helper predicate for testing/analysis */
predicate want_to_have_definition(Expr e) {
    /* not builtin object like len, tuple, etc. */ 
    not exists(Object cobj | e.refersTo(cobj) and cobj.isC()) and
    (
        e instanceof Name and e.(Name).getCtx() instanceof Load
        or
        e instanceof Attribute and e.(Attribute).getCtx() instanceof Load
        or 
        e instanceof ImportMember or
        e instanceof ImportExpr
    )
}


/* Gets the definition for 'use', if one can be found.
 */
private AstNode getADefinition(Expr use) {
    inferred_definition(use, result)
    or
    not inferred_definition(use, _) and 
    (
        self_attr_defn(use, result) 
        or
        instance_attr_defn(use, result)
        or
        local_definition(use, result)
    )
    or
    exists(ImportingStmt imp, ModuleObject mod |
        imp.contains(use) and
        use.refersTo(mod) and
        result = mod.getModule()
    )
}

private predicate preferredDefinition(AstNode preferred, AstNode other) {
    /* Prefer parameter over its default */
    preferred.(Parameter).getDefault() = other
    or
    /* Prefer definition in try-body over fall-back */
    exists(Expr use | 
        preferred = getADefinition(use) and
        other = getADefinition(use)
    ) and
    exists(Try t | 
        t.getBody().contains(preferred.(Expr))
        and
        t.getAHandler().contains(other.(Expr))
    )
    or
    /* Prefer function or class definition over call to decorator */
    preferred.(FunctionExpr).getADecoratorCall() = other
    or
    preferred.(ClassExpr).getADecoratorCall() = other
}


/** Gets the definition for 'use', if one can be found.
 * Helper for the jump-to-definition query.
 */
AstNode getDefinition(Expr use) {
    not use instanceof Call and
    not result.isArtificial() and
    not use.isArtificial() and
    result = getADefinition(use) and
    (
        strictcount(getADefinition(use)) = 1
        or
        /* If there are exactly two possibilities choose the preferred one. */
        preferredDefinition(result, getADefinition(use)) and strictcount(getADefinition(use)) = 2
        /* If more than two possibilities, then give up. It is too ambiguous. */
    )
}

