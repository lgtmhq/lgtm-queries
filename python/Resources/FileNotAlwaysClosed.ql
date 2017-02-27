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
 * @name File is not always closed
 * @description Opening a file without ensuring that it is always closed may cause resource leaks.
 * @kind problem
 * @tags efficiency
 *       correctness
 *       resources
 * @problem.severity warning
 * @sub-severity high
 * @precision high
 */

import python
import semmle.python.GuardedControlFlow

predicate opens_file(DefinitionNode f) {
    exists(ControlFlowNode func | f.getValue().(CallNode).getFunction() = func |
        exists(Object opens | 
            function_opens_file(opens) |
            func.refersTo(opens)
        )
    )
}

predicate variable_references_file(SsaVariable var, ControlFlowNode open) {
    var.getAnUltimateDefinition().getDefinition() = open and opens_file(open)
}

predicate is_not_none_guard(IsEqual isnone, ControlFlowNode open) {
     /* A guard for a file closure is also treated as a closure - The file will always be closed if not None */
     exists(ControlFlowNode close, ControlledVariable var, BasicBlock block |
           block.contains(close) and closes_or_returns_file(close, open) and variable_references_file(var, open)  |
           isnone.controls(var, block, false) and isnone.getObject(var).refersTo(theNoneObject())
     )
}

predicate is_true_guard(IsTrue istrue, ControlFlowNode open) {
     /* A guard for a file closure is also treated as a closure - The file will always be closed if bool(file) is True */
     exists(ControlFlowNode close, ControlledVariable var, BasicBlock block |
          block.contains(close) and closes_or_returns_file(close, open) and variable_references_file(var, open)  |
          istrue.controls(var, block, true)
     )
}

/** A test of the form `obj.closed` or `not obj.closed`, etc. */
predicate closed_test(ControlFlowNode test, ControlFlowNode obj, boolean sense) {
    obj = test.(AttrNode).getObject("closed") and sense = true
    or
    closed_test(test.getAPredecessor(), obj, sense.booleanNot()) and test.(UnaryExprNode).getNode().getOp() instanceof Not
}

predicate is_close(ControlFlowNode close, ControlFlowNode open) {
    opens_file(open) and
    exists(SsaVariable v |
        v.getAnUltimateDefinition().getDefinition() = open |
        /* Avoid false positives due to attribute lookup raising exceptions, treat the attribute lookup as closing the file, rather than the call */
        exists(CallNode call | call.getFunction() = close) and 
        v.getAUse() = close.(AttrNode).getObject("close")
        or
        /* A with statement closes the file */
        exists(With with |
            with.getAFlowNode() = close |
            with.getContextExpr().getAFlowNode() = v.getAUse()
        )
        or
        /* `if f.closed:` implies that the file is closed on its true edge */
        exists(ControlFlowNode branch |
            closed_test(branch, v.getAUse(), true) and close = branch.getATrueSuccessor()
            or
            closed_test(branch, v.getAUse(), false) and close = branch.getAFalseSuccessor()
        )
    )
}

predicate closes_or_returns_file(ControlFlowNode f, ControlFlowNode open) {
    is_close(f, open)
    or
    is_not_none_guard(f, open)
    or
    is_true_guard(f, open)
    or
    exists(SsaVariable v, FunctionObject closer, int arg | 
        variable_references_file(v, open) and closer.getArgumentForCall((CallNode)f, arg) = v.getAUse() and 
        function_closes_parameter(closer, arg)
    )
    or
    exists(SsaVariable v, Return ret |
        ret.getValue().getAFlowNode() = f or
        ret.getValue().contains(f.getNode()) |
        f = v.getAUse() and variable_references_file(v, open)
    )
    or
    /* If file is an argument in object construction, then file becomes that object's responsibility */
    exists(ClassObject cls | f.(CallNode).getFunction().refersTo(cls)) and
    exists(SsaVariable v |
        variable_references_file(v, open) |
        f.(CallNode).getAnArg() = v.getAUse()
    )
}

predicate function_opens_file(FunctionObject f) {
    f = theOpenFunction()
    or
    exists(SsaVariable v, Return ret | 
        ret.getScope() = f.getFunction() |
        ret.getValue().getAFlowNode() = v.getAUse() and variable_references_file(v, _)
    )
    or
    exists(Return ret, FunctionObject callee | 
        ret.getScope() = f.getFunction() |
        ret.getValue().getAFlowNode() = callee.getACall() and 
        function_opens_file(callee)
    )
}

predicate function_closes_parameter(FunctionObject func, int arg) {
    exists(SsaVariable v, CallNode call, AttrNode attr |
        func.getFunction().getArg(arg).asName() = v.getDefinition().getNode() and
        call.getFunction() = attr and
        attr.getObject() = v.getAUse() and attr.getName() = "close" and
        v.getVariable().isParameter() and v.getVariable().getScope() = func.getFunction()
    )
    or
    exists(SsaVariable v, CallNode call, FunctionObject callee |
        callee.getArgumentForCall(call, arg) = v.getAUse() and
        v.getVariable().isParameter() and
        v.getVariable().getScope() = func.getFunction() and
        function_closes_parameter(callee, arg)
    )
}

predicate edge_of_interest(ControlFlowNode p, ControlFlowNode s, boolean exceptional) {
    s = p.getASuccessor() and not s = p.getAnExceptionalSuccessor() and exceptional = false
    or
    s = p.getAnExceptionalSuccessor() and
    not ((RaisingNode)p).unlikelySuccessor(s) and
    exceptional = true
}

predicate file_is_open(ControlFlowNode f, ControlFlowNode defn, boolean exceptional) {
    not closes_or_returns_file(f, defn)
    and
    (
      opens_file(f) and f = defn and exceptional = false
      or
      exists(ControlFlowNode p, boolean e1, boolean e2 | 
          edge_of_interest(p, f, e1) and file_is_open(p, defn, e2) and
          exceptional = e1.booleanOr(e2)
      )
    )
}

/** Whether resource is opened and closed in  in a matched pair of methods,
 * either __enter__ and __exit__ or __init__ and __del__ */
predicate opened_in_enter_closed_in_exit(AttrNode open, AttrNode close) {
    opens_file(open) and
    (
        open.getScope().getName() = "__enter__" and
        close.getScope().getName() = "__exit__"
        or
        open.getScope().getName() = "__init__" and
        close.getScope().getName() = "__del__"
    ) and
    /* Both open and close refer to same attribute of the same class */
    exists(ClassObject cls, string attr_name |
        open.getObject(attr_name).refersTo(_, cls, _) and
        close.getObject(attr_name).refersTo(_, cls, _)
    ) and
    exists(CallNode call |
        call.getFunction().(AttrNode).getObject("close") = close
    )
}

predicate file_not_closed_at_scope_exit(ControlFlowNode defn, boolean exceptional)  {
    exists(Scope s, ControlFlowNode exit | 
        exit = s.getANormalExit() and
        file_is_open(exit, defn, exceptional)
        or
        exit.(RaisingNode).viableExceptionalExit(s, _) and
        file_is_open(exit, defn, _) and exceptional = true
    )
}

/* Check to see if a file is opened but not closed or returned */
from ControlFlowNode defn, string message
where
not opened_in_enter_closed_in_exit(defn, _) and
(
    file_not_closed_at_scope_exit(defn, false) and message = "File is opened but is not closed."
    or
    not file_not_closed_at_scope_exit(defn, false) and file_not_closed_at_scope_exit(defn, true) and message = "File may not be closed if an exception is raised."
)

select defn.getNode(), message
