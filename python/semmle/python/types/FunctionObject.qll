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
import semmle.python.types.Exceptions
import semmle.python.pointsto.Final
private import semmle.python.libraries.Zope

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

    /** Use descriptiveString() instead. */
    deprecated string prettyString() {
        result = this.descriptiveString()
    }

    /** Gets a longer, more descriptive version of toString() */
    abstract string descriptiveString();

    /** Gets a call-site from where this function is called as a function */
    CallNode getAFunctionCall() {
        final_function_call(this, result)
    }

    /** Gets a call-site from where this function is called as a method */
    CallNode getAMethodCall() {
        final_method_call(this, result)
    }

    /** Gets a call-site from where this function is called */
    ControlFlowNode getACall() {
        result = final_get_a_call(this)
    }

    /** Gets the `ControlFlowNode` that will be passed as the nth argument to `this` when called at `call`.
        This predicate will correctly handle `x.y()`, treating `x` as the zeroth argument.
    */
    ControlFlowNode getArgumentForCall(CallNode call, int n) {
        result = final_get_positional_argument_for_call(this, call, n)
    }

    /** Gets the `ControlFlowNode` that will be passed as the named argument to `this` when called at `call`.
        This predicate will correctly handle `x.y()`, treating `x` as the self argument.
    */
    ControlFlowNode getNamedArgumentForCall(CallNode call, string name) {
        result = final_get_named_argument_for_call(this, call, name)
    }

    /** Gets a class that this function may return */
    ClassObject getAnInferredReturnType() {
        result = final_get_an_inferred_return_type(this)
    }

    /** Whether this function never returns. This is an approximation.
     */
    predicate neverReturns() {
         final_function_never_returns(this)
    }

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
        result = final_get_a_callee(this.getFunction())
    }

    /** Gets the qualified name for this function object.
     * Should return the same name as the `__qualname__` attribute on functions in Python 3.
     */
    abstract string getQualifiedName();

    /** Whether `name` is a legal argument name for this function */
    bindingset[name]
    predicate isLegalArgumentName(string name) {
        this.getFunction().getAnArg().asName().getId() = name
        or
        this.getFunction().getAKeywordOnlyArg().getId() = name
        or
        this.getFunction().hasKwArg()
    }

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

    /** Gets a control flow node corresponding to the value of a return statement */
    ControlFlowNode getAReturnedNode() {
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
            f = this.getFunction() and
            result = count(f.getAnArg()) - count(f.getDefinition().getArgs().getADefault())
        )
    }

    int maxParameters() {
        exists(Function f |
            f = this.getFunction() and
            if exists(f.getVararg()) then
                result = 2147483647 // INT_MAX
            else
                result = count(f.getAnArg())
        )
    }

    /** Whether this method unconditionally sets the attribute `self.attrname`.
     */
    predicate unconditionallySetsSelfAttribute(string attrname) {
        final_unconditionally_sets_self_attribute(this, attrname)
    }

    string getQualifiedName() {
        result = this.getFunction().getQualifiedName()
    }

    predicate unconditionallyReturnsParameter(int n) {
        exists(SsaVariable pvar |
            exists(Parameter p | p = this.getFunction().getArg(n) |
                p.asName().getAFlowNode() = pvar.getDefinition()
            ) and
            exists(NameNode rval |
                rval = pvar.getAUse() and
                exists(Return r | r.getValue() = rval.getNode()) and
                rval.strictlyDominates(rval.getScope().getANormalExit())
            )
        )
    }

}

abstract class BuiltinCallable extends FunctionObject {

    abstract ClassObject getAReturnType();

    predicate isProcedure() {
        forex(ClassObject rt |
            rt = this.getAReturnType() |
            rt = theNoneType()
        )
    }

    abstract string getQualifiedName();

}

class BuiltinMethodObject extends BuiltinCallable {

    BuiltinMethodObject() {
        py_cobjecttypes(this, theMethodDescriptorType())
        or
        py_cobjecttypes(this, theBuiltinFunctionType()) and exists(ClassObject c | py_cmembers_versioned(c, _, this, major_version().toString()))
        or
        exists(ClassObject wrapper_descriptor | 
            py_cobjecttypes(this, wrapper_descriptor) and
            py_cobjectnames(wrapper_descriptor, "wrapper_descriptor")
        )
    }

    string getQualifiedName() {
        exists(ClassObject cls |
            py_cmembers_versioned(cls, _, this, major_version().toString()) |
            result = cls.getName() + "." + this.getName()
        )
        or
        not exists(ClassObject cls | py_cmembers_versioned(cls, _, this, major_version().toString())) and
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

    ClassObject getARaisedType() {
        /* Information is unavailable for C code in general */
        none()
    }

    predicate raisesUnknownType() {
        /* Information is unavailable for C code in general */
        any()
    }

    int minParameters() {
        none() 
    }

    int maxParameters() {
        none() 
    }

    ClassObject getAReturnType() {
        ext_rettype(this, result)
    }
    
}

class BuiltinFunctionObject extends BuiltinCallable {

    BuiltinFunctionObject() {
        py_cobjecttypes(this, theBuiltinFunctionType()) and exists(ModuleObject m | py_cmembers_versioned(m, _, this, major_version().toString()))
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

    ClassObject getARaisedType() {
        /* Information is unavailable for C code in general */
        none()
    }

    predicate raisesUnknownType() {
        /* Information is unavailable for C code in general */
        any()
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


