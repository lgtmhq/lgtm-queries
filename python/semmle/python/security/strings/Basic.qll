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

import python


import semmle.python.security.TaintTracking

/** An extensible kind of taint representing an externally controlled string.
 */
abstract class ExternalStringKind extends TaintKind {

    bindingset[this]
    ExternalStringKind() {
        this = this
    }

    override TaintKind getTaintForFlowStep(ControlFlowNode fromnode, ControlFlowNode tonode) {
        result = this and
        (
            str_method_call(fromnode, tonode) or
            slice(fromnode, tonode) or
            tonode.(BinaryExprNode).getAnOperand() = fromnode or
            os_path_join(fromnode, tonode) or
            str_format(fromnode, tonode) or
            encode_decode(fromnode, tonode) or
            to_str(fromnode, tonode)
        )
        or
        tonode.(SequenceNode).getElement(_) = fromnode and result.(ExternalStringSequenceKind).getItem() = this
        or
        json_load(fromnode, tonode) and result.(ExternalJsonKind).getValue() = this
        or
        result = this and copy_call(fromnode, tonode)
        or
        tonode.(DictNode).getAValue() = fromnode and result.(ExternalStringDictKind).getValue() = this
    }

    override ClassObject getClass() {
        result = theStrType()
    }

}

private class StringEqualitySanitizer extends Sanitizer {

    StringEqualitySanitizer() { this = "string equality sanitizer" }

    /** The test `if untrusted == "KNOWN_VALUE":` sanitizes `untrusted` on its `true` edge. */
    override predicate sanitizingEdge(TaintKind taint, PyEdgeRefinement test) {
        taint instanceof ExternalStringKind and
        exists(ControlFlowNode const, Cmpop op |
            const.getNode() instanceof StrConst |
            (
                test.getTest().(CompareNode).operands(const, op, _)
                or
                test.getTest().(CompareNode).operands(_, op, const)
            ) and (
                op instanceof Eq and test.getSense() = true
                or
                op instanceof NotEq and test.getSense() = false
            )
        )
    }

}

private predicate json_load(ControlFlowNode fromnode, CallNode tonode) {
    exists(FunctionObject json_loads |
        any(ModuleObject json | json.getName() = "json").getAttribute("loads") = json_loads and
        json_loads.getACall() = tonode and tonode.getArg(0) = fromnode
    )
}

/** A kind of "taint", representing a sequence, with a "taint" member */
class ExternalStringSequenceKind extends TaintKind {

    ExternalStringSequenceKind() {
        this = "sequence[" + any(ExternalStringKind key) + "]"
    }


    /** Gets the taint kind for item in this sequence */
    ExternalStringKind getItem() {
        this = "sequence[" + result + "]"
    }

    override TaintKind getTaintForFlowStep(ControlFlowNode fromnode, ControlFlowNode tonode) {
        this.taints(fromnode) and
        sequence_subscript_taint(tonode, fromnode, this, result)
        or
        result = this and copy_call(fromnode, tonode)
        or
        exists(BinaryExprNode mod |
            mod = tonode and 
            mod.getOp() instanceof Mod and
            mod.getAnOperand() = fromnode and
            result = this.getItem()
        )
    }

    override TaintKind getTaintOfMethodResult(string name) {
        name = "pop" and result = this.getItem()
    }

}

/** An hierachical dictionary or list where the entire structure is externally controlled
 * This is typically a parsed JSON object.
 */
class ExternalJsonKind extends TaintKind {

    ExternalJsonKind() {
        this = "json[" + any(ExternalStringKind key) + "]"
    }


    /** Gets the taint kind for item in this sequence */
    TaintKind getValue() {
        this = "json[" + result + "]"
        or
        result = this
    }

    override TaintKind getTaintForFlowStep(ControlFlowNode fromnode, ControlFlowNode tonode) {
        this.taints(fromnode) and
        json_subscript_taint(tonode, fromnode, this, result)
        or
        result = this and copy_call(fromnode, tonode)
     }

    override TaintKind getTaintOfMethodResult(string name) {
        name = "get" and result = this.getValue()
     }

}



/* A call that returns a copy (or similar) of the argument */
private predicate copy_call(ControlFlowNode fromnode, CallNode tonode) {
    tonode.getFunction().(AttrNode).getObject("copy") = fromnode
    or
    exists(ModuleObject copy, string name |
        name = "copy" or name = "deepcopy" |
        copy.getAttribute(name).(FunctionObject).getACall() = tonode and
        tonode.getArg(0) = fromnode
    )
    or
    tonode.getFunction().refersTo(builtin_object("reversed")) and
    tonode.getArg(0) = fromnode
}

/* tonode = fromnode.xxx() where the call to xxx returns an identical or similar string */
private predicate str_method_call(ControlFlowNode fromnode, CallNode tonode) {
    exists(string method_name |
        tonode.getFunction().(AttrNode).getObject(method_name) = fromnode
        |
        method_name = "strip" or method_name = "format" or
        method_name = "lstrip" or method_name = "rstrip" or
        method_name = "ljust" or method_name = "rjust" or
        method_name = "title" or method_name = "capitalize"
    )
}

/* tonode = ....format(fromnode) */
private predicate str_format(ControlFlowNode fromnode, CallNode tonode) {
    tonode.getFunction().(AttrNode).getName() = "format" and
    (
        tonode.getAnArg() = fromnode
        or
        tonode.getNode().getAKeyword().getValue() = fromnode.getNode()
    )
}

/* tonode = codec.[en|de]code(fromnode)*/
private predicate encode_decode(ControlFlowNode fromnode, CallNode tonode) {
    exists(FunctionObject func, string name |
        func.getACall() = tonode and
        tonode.getAnArg() = fromnode and
        func.getName() = name |
        name = "encode" or name = "decode" or
        name = "decodestring"
    )
}

/* tonode = str(fromnode)*/
private predicate to_str(ControlFlowNode fromnode, CallNode tonode) {
    tonode.getAnArg() = fromnode and
    exists(ClassObject str |
        tonode.getFunction().refersTo(str) |
        str = theUnicodeType() or str = theBytesType()
    )
}

/* tonode = fromnode[:] */
private predicate slice(ControlFlowNode fromnode, SubscriptNode tonode) {
    exists(Slice all |
        all = tonode.getIndex().getNode() and
        not exists(all.getStart()) and not exists(all.getStop()) and
        tonode.getValue() = fromnode
    )
}

/* tonode = os.path.join(..., fromnode, ...) */
private predicate os_path_join(ControlFlowNode fromnode, CallNode tonode) {
    exists(FunctionObject path_join |
        exists(ModuleObject os | os.getName() = "os" |
            os.getAttribute("path").(ModuleObject).getAttribute("join") = path_join
        ) |
        tonode = path_join.getACall() and tonode.getAnArg() = fromnode 
    )
}

/** A kind of "taint", representing a dictionary mapping str->"taint" */
class ExternalStringDictKind extends TaintKind {

    ExternalStringDictKind() {
        this = "dict[" + any(ExternalStringKind key) + "]"
    }

    /** Gets the taint kind for a key in this dict */
    ExternalStringKind getValue() {
        this = "dict[" + result + "]"
    }

    override TaintKind getTaintForFlowStep(ControlFlowNode fromnode, ControlFlowNode tonode) {
        this.taints(fromnode) and
        dict_subscript_taint(tonode, fromnode, this, result)
        or
        result = this and copy_call(fromnode, tonode)
    }

    override TaintKind getTaintOfMethodResult(string name) {
        name = "get" and result = this.getValue()
    }

}

/* Helper for getTaintForStep() */
pragma [noinline]
private predicate dict_subscript_taint(SubscriptNode sub, ControlFlowNode obj, ExternalStringDictKind dict, TaintKind key) {
    sub.isLoad() and
    sub.getValue() = obj and
    key = dict.getValue()
}

/* Helper for getTaintForStep() */
pragma [noinline]
private predicate sequence_subscript_taint(SubscriptNode sub, ControlFlowNode obj, ExternalStringSequenceKind seq, TaintKind key) {
    sub.isLoad() and
    sub.getValue() = obj and
    if sub.getNode().getIndex() instanceof Slice then
        seq = key
    else
        key = seq.getItem()
}

/* Helper for getTaintForStep() */
pragma [noinline]
private predicate json_subscript_taint(SubscriptNode sub, ControlFlowNode obj, ExternalJsonKind seq, TaintKind key) {
    sub.isLoad() and
    sub.getValue() = obj and
    key = seq.getValue()
}
