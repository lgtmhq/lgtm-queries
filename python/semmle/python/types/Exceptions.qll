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
 * Analysis of exception raising and handling.
 * 
 * In order to make this useful we make a number of assumptions. These are:
 * 1. Typing errors (TypeError, NameError, AttributeError) are assumed to occur only if:
 *    a) Explicitly raised, e.g. <code>raise TypeError()</code>
 *    or
 *    b) Explicitly caught, e.g. <code>except TypeError:</code>
 * 2. Asynchronous exceptions, MemoryError, KeyboardInterrupt are ignored.
 * 3. Calls to unidentified objects can raise anything, unless it is an
 *    attribute named 'read' or 'write' in which case it can raise IOError.
 */

import python

/** Subset of ControlFlowNodes which might raise an exception */
class RaisingNode extends ControlFlowNode {
    
    RaisingNode() {
        exists(this.getAnExceptionalSuccessor())
        or
        this.isExceptionalExit(_)
    }

    /** Gets the CFG node for the exception, if and only if this RaisingNode is an explicit raise */
    ControlFlowNode getExceptionNode() {
        exists(Raise r, Expr e | 
            r.getAFlowNode() = this and e = r.getException() and
            result.getBasicBlock().dominates(this.getBasicBlock()) |
            (not major_version() = 2 or not exists(e.(Tuple).getAnElt())) and result = e.getAFlowNode()
            or
            /* In Python 2 raising a tuple will result in the first element of the tuple being raised. */
            major_version() = 2 and result = e.(Tuple).getElt(0).getAFlowNode()
        )
    }

    private predicate quits() {
        this.(CallNode).getFunction().refersTo(quitterObject(_))
    }

    /** Gets the type of an exception that may be raised
        at this control flow node */
    ClassObject getARaisedType() {
        result = this.localRaisedType()
        or
        exists(FunctionObject func |
              this = func.getACall() |
              result = func.getARaisedType()
        )
        or
        result = systemExitRaise()
    }

    pragma[noinline]
    private ClassObject systemExitRaise() {
        this.quits() and result = builtin_object("SystemExit")
    }

    cached private ClassObject localRaisedType() {
        result.isSubclassOf(theBaseExceptionType()) 
        and
        (
          exists(ControlFlowNode ex |
            ex = this.getExceptionNode() and
            (ex.refersTo(result) or ex.refersTo(_, result, _))
          )
          or
          this.getNode() instanceof ImportExpr and result = builtin_object("ImportError")
          or
          this.getNode() instanceof Print and result = theIOErrorType()
          or
          exists(ExceptFlowNode except |
              except = this.getAnExceptionalSuccessor() and
              except.handles(result) |
              this.getNode() instanceof Attribute and result = theAttributeErrorType()
              or
              this.getNode() instanceof Name and result = theNameErrorType()
              or
              this.getNode() instanceof Subscript and result = theIndexErrorType()
              or
              this.getNode() instanceof Subscript and result = theKeyErrorType()
          )
          or
          not exists(ExceptFlowNode except | except = this.getAnExceptionalSuccessor())
          and
          sequence_or_mapping(this) and result = theLookupErrorType()
          or
          this.read_write_call() and result = theIOErrorType()
        )
    }

    /** Whether this control flow node raises an exception, 
     * but the type of the exception it raises cannot be inferred. */
    predicate raisesUnknownType() {
        /* read/write calls are assumed to raise IOError (OSError for Py3) */
        not this.read_write_call()
        and
        (
          /* Call to an unknown object */
          this.getNode() instanceof Call and not exists(FunctionObject func | this = func.getACall())
          and not exists(ClassObject known | this.(CallNode).getFunction().refersTo(known))
          or
          this.getNode() instanceof Exec
          or
          /* Call to a function raising an unknown type */
          exists(FunctionObject func |
              this = func.getACall() |
              func.raisesUnknownType()
          )
        )
    }

    private predicate read_write_call() {
        exists(string mname | mname = this.(CallNode).getFunction().(AttrNode).getName() |
            mname = "read" or mname = "write" 
        )
    }

    /** Whether (as inferred by type inference) it is highly unlikely (or impossible) for control to flow from this to succ.
     */
    predicate unlikelySuccessor(ControlFlowNode succ) {
        succ = this.getAnExceptionalSuccessor() and
        not this.viableExceptionEdge(succ, _) and
        not this.raisesUnknownType()
        or
        exists(FunctionObject func |
            func.getACall() = this and
            func.neverReturns() and
            succ = this.getASuccessor() and
            not succ = this.getAnExceptionalSuccessor()
        )
        or
        this.quits() and 
        succ = this.getASuccessor() and
        not succ = this.getAnExceptionalSuccessor()
    }

    /** Whether it is considered plausible that 'raised' can be raised across the edge this-succ */
    predicate viableExceptionEdge(ControlFlowNode succ, ClassObject raised) {
        raised.isLegalExceptionType() and
        raised = this.getARaisedType() and
        succ = this.getAnExceptionalSuccessor() and
        ( 
            /* An 'except' that handles raised and there is no more previous handler */
            ((ExceptFlowNode)succ).handles(raised) and 
            not exists(ExceptFlowNode other, StmtList s, int i, int j | 
                not other = succ and other.handles(raised) and
                s.getItem(i) = succ.getNode() and s.getItem(j) = other.getNode()
                |
                j < i
            )
            or
            /* Any successor that is not an 'except', provided that 'raised' is not handled by a different successor. */
            (not ((ExceptFlowNode)this.getAnExceptionalSuccessor()).handles(raised) and
             not succ instanceof ExceptFlowNode)
        )
    }

    /** Whether this exceptional exit is viable. That is, is it
     * plausible that the scope `s` can be exited with exception `raised`
     * at this point.
     */
    predicate viableExceptionalExit(Scope s, ClassObject raised) {
        raised.isLegalExceptionType() and
        raised = this.getARaisedType() and
        this.isExceptionalExit(s) and
        not ((ExceptFlowNode)this.getAnExceptionalSuccessor()).handles(raised)
    }

}

/** Is this a sequence or mapping subscript x[i]? */
private predicate sequence_or_mapping(RaisingNode r) {
    r.getNode() instanceof Subscript
}

private predicate current_exception(ClassObject ex, BasicBlock b) {
    exists(RaisingNode r |
        r.viableExceptionEdge(b.getNode(0), ex) and not b.getNode(0) instanceof ExceptFlowNode
    )
    or
    exists(BasicBlock prev | 
        current_exception(ex, prev) and
        exists(ControlFlowNode pred, ControlFlowNode succ |
            pred = prev.getLastNode() and succ = b.getNode(0) |
            pred.getASuccessor() = succ and 
            (/* Normal control flow */
             not pred.getAnExceptionalSuccessor() = succ or 
             /* Re-raise the current exception, propagating to the successor */
             pred instanceof ReraisingNode)
        )
    )
}

private predicate unknown_current_exception(BasicBlock b) {
    exists(RaisingNode r |
        r.raisesUnknownType() and 
        r.getAnExceptionalSuccessor() = b.getNode(0) and
        not b.getNode(0) instanceof ExceptFlowNode
    )
    or
    exists(BasicBlock prev | 
        unknown_current_exception(prev) and
        exists(ControlFlowNode pred, ControlFlowNode succ |
            pred = prev.getLastNode() and succ = b.getNode(0) |
            pred.getASuccessor() = succ and 
            (not pred.getAnExceptionalSuccessor() = succ or pred instanceof ReraisingNode)
        )
    )
}

/** INTERNAL -- Use FunctionObject.getARaisedType() instead */
predicate scope_raises(ClassObject ex, Scope s) {
    exists(BasicBlock b | 
        current_exception(ex, b) and
        b.getLastNode().isExceptionalExit(s) |
        b.getLastNode() instanceof ReraisingNode
    )
    or
    exists(RaisingNode r | r.viableExceptionalExit(s, ex))
}

/** INTERNAL -- Use FunctionObject.raisesUnknownType() instead */
predicate scope_raises_unknown(Scope s) {
    exists(BasicBlock b | 
        b.getLastNode() instanceof ReraisingNode
        and b.getLastNode().isExceptionalExit(s) |
        unknown_current_exception(b)
    )
    or
    exists(RaisingNode r |
        r.raisesUnknownType() and
        r.isExceptionalExit(s)
    )
}


/** ControlFlowNode for an 'except' statement. */
class ExceptFlowNode extends ControlFlowNode {

    ExceptFlowNode() {
        this.getNode() instanceof ExceptStmt
    }

    private predicate handledObject(Object obj, ClassObject cls, ControlFlowNode origin) {
        exists(ExceptStmt ex, ControlFlowNode type |
            this.getBasicBlock().dominates(type.getBasicBlock()) and
            ex = this.getNode() and type = ex.getType().getAFlowNode() and
            type.refersTo(obj, cls, origin)
        )
        or
        exists(Object tup |
            this.handledObject(tup, theTupleType(), _) |
            element_from_tuple(tup).refersTo(obj, cls, origin)
        )
    }

    /** Gets the inferred type(s) that are handled by this node, splitting tuples if possible. */
    cached predicate handledException(Object obj, ClassObject cls, ControlFlowNode origin) {
        this.handledObject(obj, cls, origin) and not cls = theTupleType()
        or
        not exists(this.getNode().(ExceptStmt).getType()) and obj = theBaseExceptionType() and cls = theTypeType() and
        origin = this
    }

    /** Whether this `except` handles `cls` */
    predicate handles(ClassObject cls) {
        exists(ClassObject handled |
            this.handledException(handled, _, _) |
            cls.getAnImproperSuperType() = handled
        )
    }

}

private ControlFlowNode element_from_tuple(Object tuple) {
    exists(Tuple t |
        t = tuple.getOrigin() and result = t.getAnElt().getAFlowNode()
    )
}

/** A Reraising node is the node at the end of a finally block (on the exceptional branch)
 * that reraises the current exception.
 */
class ReraisingNode extends RaisingNode {

    ReraisingNode() {
        not this.getNode() instanceof Raise and
        in_finally(this) and
        forall(ControlFlowNode succ |
            succ = this.getASuccessor() |
            succ = this.getAnExceptionalSuccessor()
        )
    }

    /** Gets a class that may be raised by this node */
    ClassObject getARaisedType() {
        exists(BasicBlock b |
            current_exception(result, b) and
            b.getNode(_) = this
        )
    }

}

private predicate in_finally(ControlFlowNode n) {
    exists(Stmt f | 
        exists(Try t | f = t.getAFinalstmt()) |
        f = n.getNode() 
        or
        f.containsInScope(n.getNode())
    )
}



