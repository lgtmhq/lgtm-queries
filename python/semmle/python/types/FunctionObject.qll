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
import semmle.python.types.Exceptions
private import Attributes

/** A function object, whether written in Python or builtin */
abstract class FunctionObject extends Object {

    predicate isOverridingMethod() {
        exists(Object f | this.overrides(f))
    }

    predicate isOverriddenMethod() {
        exists(Object f | f.overrides(this))
    }

    Function getFunction() {
        result = ((CallableExpr)this.getOrigin()).getInnerScope()
    }

    /** This function always returns None, meaning that its return value should be disregarded */
    abstract predicate isProcedure();

    /** Gets the name of this function */
    abstract string getName();

    /** Gets a class that may be raised by this function */
    abstract ClassObject getARaisedType();

    /** Whether this function raises an exception, the class of which cannot be inferred */
    abstract predicate raisesUnknownType();

    /** Whether this function never returns */
    abstract predicate neverReturns();

    /** Use descriptiveString() instead. */
    deprecated string prettyString() {
        result = this.descriptiveString()
    }

    /** Gets a longer, more descriptive version of toString() */
    abstract string descriptiveString();

    /** Gets a call-site from where this function is called as a function */
    CallNode getAFunctionCall() {
        result.getFunction().refersTo(this)
    }

    /** Gets a call-site from where this function is called as a method */
    CallNode getAMethodCall() {
        exists(ControlFlowNode attr, ClassObject cls, string name |
            attr = result.getFunction() and
            receiverTypeFor(attr, cls, name) and
            this = cls.lookupAttribute(name)
        )
        or
        super_method_call(result, this)
    }

    /** Gets a call-site from where this function is called */
    ControlFlowNode getACall() {
        result = this.getAFunctionCall()
        or
        result = this.getAMethodCall()
    }

    /** Gets the `ControlFlowNode` that will be passed as the nth argument to `this` when called at `call`.
        This predicate will correctly handle `x.y()`, treating `x` as the zeroth argument.
    */
    ControlFlowNode getArgumentForCall(CallNode call, int n) {
        call = this.getAMethodCall() and
        (
            exists(int call_index | n = call_index+1 | result = call.getArg(call_index))
            or
            n = 0 and result = call.getFunction().(AttrNode).getObject()
        )
        or
        call = this.getAFunctionCall() and
        result = call.getArg(n)
    }

    /** Gets a class that this function may return */
    abstract ClassObject getAnInferredReturnType();

    /** Whether this is a "normal" method, that is, it is exists as a class attribute 
     *  which is not wrapped and not the __new__ method. */
    predicate isNormalMethod() {
        exists(ClassObject cls, string name |
            cls.declaredAttribute(name) = this and
            name != "__new__" and
            not this.getOrigin() instanceof Lambda
        )
    }

    /** Gets the minimum number of parameters that can be correctly passed to this function */
    abstract int minParameters();

    /** Gets the maximum number of parameters that can be correctly passed to this function */
    abstract int maxParameters();

    /** Gets a function that this function (directly) calls */
    FunctionObject getACallee() {
        exists(ControlFlowNode node, Function f |
            node.getScope() = f and
            f = this.getFunction() and
            node = result.getACall()
        )
    }

    /** Gets the qualified name for this function object.
     * Should return the same name as the `__qualname__` attribute on functions in in Python 3.
     */
    abstract string getQualifiedName();

}

/**
 * Whether this class is the receiver type of an attribute access.
 *  Also bind the name of the attribute.
 */
predicate receiverTypeFor(ControlFlowNode n, ClassObject cls, string name) {
    /* `super().meth()` is not a method on `super` */
    cls != theSuperType() and
    exists(Object o |
        /* list.__init__() is not a call to type.__init__() */
        not o instanceof ClassObject |
        n.(AttrNode).getObject(name).refersTo(o, cls, _)
    )
    or
    exists(PlaceHolder p, Variable v | 
        n.getNode() = p and n.(NameNode).uses(v) and name = v.getId() and
        p.getScope().getScope() = cls.getPyClass()
    )
}

/** Whether `call` is a call to `method` of the form `super(...).method(...)` */
private predicate super_method_call(CallNode call, FunctionObject method) {
    exists(AttrNode attr |
        attr = call.getFunction() and
        exists(CallNode super_call, ClassObject start_type, ClassObject self_type, string name |
            super_call_types(super_call, self_type, start_type) |
            super_call = attr.getObject(name) and
            /* super().name lookup */
            self_type.lookupMro(start_type, name) = method
        )
    )
}

class PyFunctionObject extends FunctionObject {

    PyFunctionObject() {
        this.getOrigin() instanceof CallableExpr
    }

    string toString() {
        result = "Function " + this.getName()
    }

    string getName() {
        result = ((FunctionExpr)this.getOrigin()).getName()
        or
        this.getOrigin() instanceof Lambda and result = "lambda"
    }

    /** Whether this function is a procedure, that is, it has no explicit return statement and is not a generator function */
    predicate isProcedure() {
        this.getFunction().isProcedure()
    }

    ClassObject getARaisedType() {
        scope_raises(result, this.getFunction())
    }

    predicate raisesUnknownType() {
        scope_raises_unknown(this.getFunction())
    }

    /** Whether this function never returns. This is an approximation.
     */
    predicate neverReturns() {
        /* A function never returns if it has no normal exits that are not dominated by a
         * call to a function which itself never returns.
         */
        exists(Function f | f = this.getFunction() |
            not exists(ControlFlowNode exit |
                exit = f.getANormalExit()
                and
                not exists(FunctionObject callee, BasicBlock call  |
                    callee.getACall().getBasicBlock() = call and
                    callee.neverReturns() and
                    call.dominates(exit.getBasicBlock())
                )
            )
        )
    }

    ClassObject getAnInferredReturnType() {
        this.getFunction().isGenerator() and result = theGeneratorType()
        or
        not this.neverReturns() and not this.getFunction().isGenerator() and
        (
          this.getAReturnedNode().refersTo(_, result, _)
          or
          this.implicityReturns(result)
          or 
          /* If the origin of the the return node is a call to another function, then this function will return the type of that call 
           * Note: since runtime_points_to() is intra-procedural, we need to handle the return types of calls explicitly here. */
          exists(FunctionObject callee |
              runtime_points_to(this.getAReturnedNode(), _, theUnknownType(), callee.getACall()) | 
              result = callee.getAnInferredReturnType()
          )
        )
    }

    /**
     * Whether this implictly returns an object
     */
    pragma[noinline]
    private predicate implicityReturns(ClassObject none) {
       none = theNoneType() and
       (
         not exists(this.getAReturnedNode())
         or
         exists(Return ret | ret.getScope() = this.getFunction() and not exists(ret.getValue()))
       )
    }

    private ControlFlowNode getAReturnedNode() {
        exists(Return ret |
            ret.getScope() = this.getFunction() and
            result.getNode() = ret.getValue()
        )
    }

    string descriptiveString() {
        if this.getFunction().isMethod() then (
            exists(Class cls | 
                this.getFunction().getScope() = cls |
                result = "method " + this.getQualifiedName()
            )
        ) else (
            result = "function " + this.getQualifiedName()
        )
    }

    int minParameters() {
        exists(Function f |
            f = this.getFunction() |
            result = count(f.getAnArg()) - count(f.getDefinition().getArgs().getADefault())
        )
    }

    int maxParameters() {
        exists(Function f |
            f = this.getFunction() |
            if exists(f.getVararg()) then
                result = 2147483647 // INT_MAX
            else
                result = count(f.getAnArg())
        )
    }

    /** Whether this method unconditionally sets the attribute `self.attrname`.
     */
    predicate unconditionallySetsSelfAttribute(string attrname) {
        unconditionally_sets_self_attribute(this, attrname)
    }

    string getQualifiedName() {
        result = this.getFunction().getQualifiedName()
    }

}

class BuiltinMethodObject extends FunctionObject {

    BuiltinMethodObject() {
        py_cobjecttypes(this, theMethodDescriptorType())
        or
        py_cobjecttypes(this, theBuiltinFunctionType()) and exists(ClassObject c | py_cmembers(c, _, this))
        or
        exists(ClassObject wrapper_descriptor | 
            py_cobjecttypes(this, wrapper_descriptor) and
            py_cobjectnames(wrapper_descriptor, "wrapper_descriptor")
        )
    }

    string getQualifiedName() {
        exists(ClassObject cls |
            py_cmembers(cls, _, this) |
            result = cls.getName() + "." + this.getName()
        )
        or
        not exists(ClassObject cls | py_cmembers(cls, _, this)) and
        result = this.getName()
    }

    string descriptiveString() {
        result = "builtin-method " + this.getQualifiedName()
    }

    string getName() {
        py_cobjectnames(this, result)
    }

    string toString() {
        result = "Builtin-method " + this.getName()
    }

    predicate isProcedure() {
        this.getAnInferredReturnType() = theNoneType()
    }

    ClassObject getARaisedType() {
        /* Information is unavailable for C code in general */
        none()
    }

    predicate raisesUnknownType() {
        /* Information is unavailable for C code in general */
        any()
    }

    predicate neverReturns() {
        none()
    }

    ClassObject getAnInferredReturnType() {
        ext_rettype(this, result)
    }

    int minParameters() {
        none() 
    }

    int maxParameters() {
        none() 
    }

}

class BuiltinFunctionObject extends FunctionObject {

    BuiltinFunctionObject() {
        py_cobjecttypes(this, theBuiltinFunctionType()) and exists(ModuleObject m | py_cmembers(m, _, this))
    }

    string getName() {
        py_cobjectnames(this, result)
    }

    string getQualifiedName() {
        result = this.getName()
    }

    string toString() {
        result = "Builtin-function " + this.getName()
    }

    string descriptiveString() {
        result = "builtin-function " + this.getName()
    }

    predicate isProcedure() {
        this.getAnInferredReturnType() = theNoneType()
    }

    ClassObject getARaisedType() {
        /* Information is unavailable for C code in general */
        none()
    }

    predicate raisesUnknownType() {
        /* Information is unavailable for C code in general */
        any()
    }

    predicate neverReturns() {
        this = theExitFunctionObject()
    }

    ClassObject getAnInferredReturnType() {
        result = this.getAReturnType() 
    }

    ClassObject getAReturnType() {
        /* Enumerate the types of a few builtin functions, that the CPython analysis misses.
        */
        this = builtin_object("hex") and result = theStrType()
        or
        this = builtin_object("oct") and result = theStrType()
        or
        this = builtin_object("intern") and result = theStrType()
        or
        /* Fix a few minor inaccuracies in the CPython analysis */ 
        ext_rettype(this, result) and not (
            this = builtin_object("__import__") and result = theNoneType()
            or
            this = builtin_object("compile") and result = theNoneType()
            or
            this = builtin_object("sum")
        )
    }

    int minParameters() {
        none() 
    }

    int maxParameters() {
        none() 
    }

}


