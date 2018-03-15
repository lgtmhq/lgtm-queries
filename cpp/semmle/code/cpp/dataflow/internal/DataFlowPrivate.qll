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

private import cpp
private import DataFlowUtil

/** Gets the instance argument of a non-static call. */
private Node getInstanceArgument(Call call) {
  result.asExpr() = call.getQualifier()
  // This does not include the implicit `this` argument on auto-generated
  // base class destructor calls as those do not have an AST element.
}

/**
 * A data flow node that occurs as the argument of a call and is passed as-is
 * to the callable. Arguments that are wrapped in an implicit varargs array
 * creation are not included, but the implicitly created array is.
 * Instance arguments are also included.
 */
class ArgumentNode extends Node {
  ArgumentNode() {
    exists(Argument arg | this.asExpr() = arg) or
    this = getInstanceArgument(_)
  }

  /**
   * Holds if this argument occurs at the given position in the given call.
   * The instance argument is considered to have index `-1`.
   */
  predicate argumentOf(Call call, int pos) {
    exists(Argument arg | this.asExpr() = arg | call = arg.getCall() and pos = arg.getPosition()) or
    pos = -1 and this = getInstanceArgument(call)
  }
}

/** A data flow node that occurs as the result of a `ReturnStmt`. */
class ReturnNode extends ExprNode {
  ReturnNode() {
    exists(ReturnStmt ret | this.getExpr() = ret.getExpr())
  }
}

/**
 * Holds if data can flow from `node1` to `node2` in a way that loses the
 * calling context. For example, this would happen with flow through a
 * global or static variable.
 */
predicate jumpStep(Node n1, Node n2) {
  none()
}

/**
 * Holds if `call` does not pass an implicit or explicit qualifier, i.e., a
 * `this` parameter.
 */
predicate callHasQualifier(Call call) {
  call.hasQualifier()
  or
  call.getTarget() instanceof Destructor
}

//////////////////////////////////////////////////////////////////////////////
// Java QL library compatibility wrappers
//////////////////////////////////////////////////////////////////////////////

/** An argument to a call. */
class Argument extends Expr {
  Call call;
  int pos;

  Argument() {
    call.getArgument(pos) = this
  }

  /** Gets the call that has this argument. */
  Call getCall() { result = call }

  /** Gets the position of this argument. */
  int getPosition() {
    result = pos
  }
}

class Callable extends Function { }

/**
 * An alias for `Function` in the C++ library. In the Java library, a `Method`
 * is any callable except a constructor.
 */
class Method extends Function { }

/**
 * An alias for `FunctionCall` in the C++ library. In the Java library, a
 * `MethodAccess` is any `Call` that does not call a constructor.
 */
class MethodAccess extends FunctionCall {
  /**
   * INTERNAL: Do not use. Alternative name for `getEnclosingFunction`.
   */
  Callable getEnclosingCallable() {
    result = this.getEnclosingFunction()
  }
}
