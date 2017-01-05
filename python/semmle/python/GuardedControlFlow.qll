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

import python
private import semmle.python.pointsto.Penultimate

class ConditionalControlFlowNode extends ControlFlowNode {

    ConditionalControlFlowNode() {
        is_condition(this)
    }

    /** Gets the truth value of the sub-condition 'cond' given that this condition evaluates to 'thisIsTrue'. */
    boolean isTrueOfSubCondition(ConditionalControlFlowNode cond, boolean thisIsTrue) {
        cond = this and result = true and thisIsTrue = true
        or
        cond = this and result = false and thisIsTrue = false
        or
        result = this.(UnaryExprNode).getOperand().(ConditionalControlFlowNode).isTrueOfSubCondition(cond, true) and thisIsTrue = false and is_not(this)
        or
        result = this.(UnaryExprNode).getOperand().(ConditionalControlFlowNode).isTrueOfSubCondition(cond, false) and thisIsTrue = true and is_not(this)
    }

    /** Whether this condition ensures that 'cond' is condIsTrue in block */
    private predicate ensuresThat(ConditionalControlFlowNode cond, BasicBlock block, boolean condIsTrue) {
        exists(boolean thisIsTrue |
            condIsTrue = this.isTrueOfSubCondition(cond, thisIsTrue)
            and
            exists(ConditionBlock control | control.controls(block, thisIsTrue) and control.getLastNode() = this)
         )
    }

    private boolean isTrueInBlock(BasicBlock block) {
        exists(ConditionalControlFlowNode cond | cond.ensuresThat(this, block, result))
    }

    /** Gets the sense in which this condition applies to `var`. 
     * For example, consider a class which represents tests for whether a variable is zero.
     * For a test `x == 0` this should return `true` for `x`, whereas for the test `x != 0` it should return `false`. */
    abstract boolean isTrueFor(ControlledVariable var);

    /** Gets the sense in which this condition applies to the attribute `var.attr_name` */
    abstract boolean isTrueForAttribute(SsaVariable var, string attr_name);

    /** Whether this condition controls the basic block `block` for the variable `var` when the condition evaluates to condIsTrue */
    predicate controls(ControlledVariable var, BasicBlock block, boolean condIsTrue) {
        condIsTrue = this.isTrueFor(var).booleanXor(this.isTrueInBlock(block)).booleanNot()
    }

    /** Whether this condition controls the basic block `block` for the attribute `name` of variable `var` when the condition evaluates to condIsTrue */
    predicate controlsAttribute(SsaVariable var, string name, BasicBlock block, boolean condIsTrue) {
        condIsTrue = this.isTrueForAttribute(var, name).booleanXor(this.isTrueInBlock(block)).booleanNot()
    }

    /** Whether this condition controls the edge from pred->succ for the variable `var` when the condition evaluates to condIsTrue */
    pragma[nomagic]
    predicate controlsEdge(ControlledVariable var, BasicBlock pred, BasicBlock succ, boolean condIsTrue) {
        /* If block is controlled, then its immediately following edges must also be controlled */
        this.controls(var, pred, condIsTrue) and succ = pred.getASuccessor() 
        or
        /* Case for immediate successor edges, accounting for negation. */
        exists(ConditionalControlFlowNode cond |
            /* Note that the branch is from the outer condition.
             * E.g. for the condition `not not test()` the branch is from the leftmost (final) `not`. */ 
            pred = cond.getBasicBlock() |
            cond.isTrueOfSubCondition(this, this.isTrueFor(var)) = condIsTrue and succ = cond.getATrueSuccessor()
            or
            cond.isTrueOfSubCondition(this, this.isTrueFor(var)).booleanNot() = condIsTrue and succ = cond.getAFalseSuccessor()
        )
    }

    /** Whether this condition applies to node: Does this condition hold at `node` and is its value `condIsTrue`? */
    predicate appliesTo(ControlledVariable var, ControlFlowNode node, boolean condIsTrue) {
        exists(BasicBlock b |
            /* Only applies if the variable has not been reassigned */
            var.immutableInScope(b.getScope()) and
            var.getAUse() = node and node.getBasicBlock() = b |
            this.controls(var, b, condIsTrue)
        )
        or
        exists(string name, BasicBlock b |
            /* Only applies if the attribute has not been changed */
            attributeNotMutated(var, name) and
            var.getAUse() = node.(AttrNode).getObject(name) and 
            node.getBasicBlock() = b |
            this.controlsAttribute(var.(SsaVariable), name, b, condIsTrue)
        )
    }

}

private predicate is_not(ControlFlowNode unary) {
    exists(UnaryExpr u | unary.getNode() = u and u.getOp() instanceof Not)
}

/** A basic block which terminates in a condition, splitting the subsequent control flow */
class ConditionBlock extends BasicBlock {

    ConditionBlock() {
       exists(ControlFlowNode succ | succ = this.getATrueSuccessor() or succ = this.getAFalseSuccessor())
    }

    /** Basic blocks controlled by this condition, i.e. those BBs for which the condition is testIsTrue */
    predicate controls(BasicBlock controlled, boolean testIsTrue) {
        /* For this block to control the block 'controlled' with 'testIsTrue' the following must be true:
           Execution must have passed through the test i.e. 'this' must strictly dominate 'controlled'.
           Execution must have passed through the 'testIsTrue' edge leaving 'this'.
           
           Although "passed through the true edge" implies that this.getATrueSuccessor() dominates 'controlled',
           the reverse is not true, as flow may have passed through another edge to get to this.getATrueSuccessor()
           so we need to assert that this.getATrueSuccessor() dominates 'controlled' *and* that 
           all predecessors of this.getATrueSuccessor() are either this or dominated by this.getATrueSuccessor().
           
           For example, in the following python snippet:
           <code>
              if x:
                  controlled
              false_successor
              uncontrolled
           </code>
           false_successor dominates uncontrolled, but not all of its predecessors are this (if x) 
           or dominated by itself. Whereas in the following code:
           <code>
              if x:
                  while controlled:
                      also_controlled
              false_successor
              uncontrolled
           </code>
           the block 'while controlled' is controlled because all of its predecessors are this (if x) 
           or (in the case of 'also_controlled') dominated by itself.
           
           The additional constraint on the predecessors of the test successor implies
           that `this` strictly dominates `controlled` so that isn't necessary to check
           directly.
        */
        exists(BasicBlock succ | 
            testIsTrue = true and succ = this.getATrueSuccessor()
            or
            testIsTrue = false and succ = this.getAFalseSuccessor()
            |
            succ.dominates(controlled) and 
            forall(BasicBlock pred | pred.getASuccessor() = succ |
                pred = this or succ.dominates(pred)
            )
        )
    }

}

/* Python specific part */

/** Union of SsaVariable, non-local and global variables */
class ControlledVariable extends @py_base_var {

    ControlledVariable() {
        this instanceof SsaVariable and not this.(SsaVariable).getVariable() instanceof GlobalVariable
        or
        this instanceof GlobalVariable
        or
        this.(Variable).getAnAccess().getScope() != this.(Variable).getScope()
    }

    string toString() {
         result = ((SsaVariable)this).toString()
         or
         result = ((Variable)this).toString()
    }

    Variable getVariable() {
        result = this.(SsaVariable).getVariable()
        or
        result = this
    }

    string getId() {
         result = ((SsaVariable)this).getId()
         or
         result = ((Variable)this).getId()
    }

    ControlFlowNode getAUse() {
        result = ((SsaVariable)this).getAUse()
        or
        result.getNode() = ((Variable)this).getALoad()
    }

    /** Whether this variable is not modified in the scope of use, or an inner scope */
    predicate immutableInScope(Scope s) {
        this.(SsaVariable).getVariable().getScope() = s
        or
        this.(Variable).getAnAccess().getScope() = s and
        not scope_of_definition(this).getScope*() = s
    }

}

private Scope scope_of_definition(Variable v) {
    exists(Name def |
        def.defines(v) and def.getScope() = result
    )
}


private predicate is_condition(ControlFlowNode guard) {
    exists(guard.getATrueSuccessor()) or
    exists(guard.getAFalseSuccessor()) or
    exists(UnaryExprNode not_ | is_not(not_) and is_condition(not_) and not_.getOperand() = guard)
}

private predicate attributeNotMutated(SsaVariable var, string name) {
    exists(AttrNode use | use.getObject(name) = var.getAUse())
    and
    not exists(AttrNode defn |
        defn.getObject(name) = var.getAUse() |
        defn.isStore()
    )
}

/** A condition which determines whether a variable evaluates to True */
class IsTrue extends ConditionalControlFlowNode {

    IsTrue() {
        exists(ControlledVariable var | var.getAUse() = this)
        or
        exists(SsaVariable var | var.getAUse() = this.(AttrNode).getObject())
    }

    boolean isTrueFor(ControlledVariable var) {
        var.getAUse() = this and result = true
    }

    boolean isTrueForAttribute(SsaVariable var, string attr_name) {
        this.(AttrNode).getObject(attr_name) = var.getAUse() and result = true
    }
    
    abstract ControlFlowNode getRelevantUse(ControlledVariable var);

}

abstract class PenultimatePointsToFilter extends ConditionalControlFlowNode {

    predicate allowedValue(ControlledVariable var, Object value) { none() }

    predicate allowedClass(ClassObject cls) { none() }
     
    abstract ControlFlowNode getRelevantUse(ControlledVariable var);

}

/** A condition which determines whether a isinstance(variable, cls) is true */
class IsInstance extends PenultimatePointsToFilter {

    IsInstance() {
        isinstance(this, _, _, _) or
        isinstance(this, _, _, _, _)
    }

    boolean isTrueFor(ControlledVariable var) {
        isinstance(this, var, _, _) and result = true
    }

    boolean isTrueForAttribute(SsaVariable var, string attr_name) {
        isinstance(this, var, attr_name, _, _) and result = true
    }

    /** Gets the `ControlFlowNode` of the class in this `isinstance` check */
    ControlFlowNode getClass() {
        isinstance(this, _, result, _) or
        isinstance(this, _, _, result, _)
    }

    predicate allowedClass(ClassObject cls) {
        exists(Object cls_or_tuple, ClassObject scls |
            scls = penultimate_get_an_improper_super_type(cls) and
            penultimate_points_to(this.getClass(), cls_or_tuple, _, _) |
            /* cls_or_tuple is a class */
            cls_or_tuple = scls
            or
            penultimate_points_to(cls_or_tuple.(TupleNode).getElement(_), scls, _, _)
        )
    }
    
    ControlFlowNode getRelevantUse(ControlledVariable var) {
         isinstance(this, var, _, result)
         or
         isinstance(this, var, _, _, result)
    }

}

private predicate isinstance(CallNode fc, ControlledVariable var, ControlFlowNode cls, ControlFlowNode use) {
    fc.getFunction().(NameNode).getId() = "isinstance" and
    cls = fc.getArg(1) and fc.getArg(0) = use and use = var.getAUse()
}

private predicate isinstance(CallNode fc, SsaVariable var, string attr_name, ControlFlowNode cls, ControlFlowNode use) {
    fc.getFunction().(NameNode).getId() = "isinstance" and
    cls = fc.getArg(1) and fc.getArg(0).(AttrNode).getObject(attr_name) = use and use = var.getAUse()
}


/** A condition which determines whether a issubclass(variable, cls) is true */
class IsSubclass extends PenultimatePointsToFilter {

    IsSubclass() {
        issubclass(this, _, _, _) or
        issubclass(this, _, _, _, _)
    }

    boolean isTrueFor(ControlledVariable var) {
        issubclass(this, var, _, _) and result = true
    }

    boolean isTrueForAttribute(SsaVariable var, string attr_name) {
        issubclass(this, var, attr_name, _, _) and result = true
    }

    /** Gets the `ControlFlowNode` node of the class in this `issubclass` check */
    ControlFlowNode getClass(ControlledVariable var) {
        issubclass(this, var, result, _) or
        issubclass(this, var, _, result, _)
    }

    predicate allowedValue(ControlledVariable var, Object value) {
        exists(ClassObject scls |
            penultimate_points_to(this.getClass(var), scls, _, _) |
            scls = penultimate_get_an_improper_super_type(value)
        )
    }
    
    ControlFlowNode getRelevantUse(ControlledVariable var) {
       issubclass(this, var, _, result)
    }

}

private predicate issubclass(CallNode fc, ControlledVariable var, ControlFlowNode cls, ControlFlowNode use) {
    fc.getFunction().(NameNode).getId() = "issubclass" and
    fc.getArg(0) = use and use = var.getAUse() and cls = fc.getArg(1)
}

private predicate issubclass(CallNode fc, SsaVariable var, string attr_name, ControlFlowNode cls, ControlFlowNode use) {
    fc.getFunction().(NameNode).getId() = "issubclass" and
    fc.getArg(0).(AttrNode).getObject(attr_name) = use and use = var.getAUse() and cls = fc.getArg(1)
}

/** A condition which determines whether a callable(variable) is true */
class IsCallable extends PenultimatePointsToFilter {

    IsCallable() {
        is_callable(this, _)
    }

    boolean isTrueFor(ControlledVariable var) {
        is_callable(this, var.getAUse()) and result = true
    }

    boolean isTrueForAttribute(SsaVariable var, string name) {
        exists(AttrNode attr |
            is_callable(this, attr) and 
            attr.getObject(name) = var.getAUse() and
            result = true
        )
    }

    predicate allowedClass(ClassObject cls) {
        penultimate_class_has_attribute(cls, "__call__")
    }
    
    ControlFlowNode getRelevantUse(ControlledVariable var) {
       is_callable(this, result) and var.getAUse() = result
    }

}

private predicate is_callable(CallNode c, ControlFlowNode obj) {
    c.getFunction().(NameNode).getId() = "callable" and
    obj = c.getArg(0)
}


/** A condition which determines whether a variable is equal to a particular object.
 *  We treat x is y and x == y as equivalence.
 */
class IsEqual extends PenultimatePointsToFilter {

    IsEqual() {
        exists(ControlledVariable var |
            equality_test(this, var.getAUse(), _, _)
        )
    }

    boolean isTrueFor(ControlledVariable var) {
        equality_test(this, var.getAUse(), result, _)
    }

    boolean isTrueForAttribute(SsaVariable var, string name) {
        exists(AttrNode attr |
            equality_test(this, attr, result, _) |
            attr.getObject(name) = var.getAUse()
        )
    }

    /** Gets the expression that this variable is equals to. */
    ControlFlowNode getObject(ControlledVariable var) {
         equality_test(this, var.getAUse(), _, result)
    }

    predicate allowedValue(ControlledVariable var, Object value) {
        penultimate_points_to(this.getObject(var), value, _, _)
    }
    
    ControlFlowNode getRelevantUse(ControlledVariable var) {
        equality_test(this, result, _, _) and var.getAUse() = result
    }
    
}

private predicate equality_test(CompareNode c, ControlFlowNode x, boolean is, ControlFlowNode y) {
    exists(Cmpop op |
        c.operands(x, op, y) or
        c.operands(y, op, x)
        |
        (is = true and op instanceof Is or
         is = false and op instanceof IsNot or
         is = true and op instanceof Eq or
         is = false and op instanceof NotEq
        )
    )
}


/** A condition which determines whether a call to hasattr(variable, name) is true */
class HasAttr extends PenultimatePointsToFilter {

    HasAttr() {
        hasattr(this, _, _)
    }

    boolean isTrueFor(ControlledVariable var) {
        hasattr(this, var.getAUse(), _) and result = true
    }

    boolean isTrueForAttribute(SsaVariable var, string name) {
        exists(AttrNode attr |
            hasattr(this, attr, _) and 
            attr.getObject(name) = var.getAUse() and
            result = true
        )
    }

    /** Gets the attribute name checked for by this `hasattr()` test */
    string getAttr() {
        hasattr(this, _, result)
    }

    predicate allowedClass(ClassObject cls) {
        exists(string attr |
            this.getAttr() = attr and
            penultimate_class_has_attribute(cls, attr)
        )
    }
    
    ControlFlowNode getRelevantUse(ControlledVariable var) {
        hasattr(this, result, _) and var.getAUse() = result
    }
    
}

private predicate hasattr(CallNode c, ControlFlowNode obj, string attr) {
    c.getFunction().getNode().(Name).getId() = "hasattr" and
    c.getArg(0) = obj and
    c.getArg(1).getNode().(StrConst).getText() = attr
}

