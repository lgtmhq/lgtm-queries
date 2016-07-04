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

/**
 * @name Equals on incomparable types
 * @description Calls of the form 'x.equals(y)', where the types of 'x' and 'y' are incomparable,
 *              should always return 'false'.
 * @kind problem
 * @problem.severity error
 */
import default

/** A call to an `equals` method. */
class EqualsCall extends MethodAccess {
  EqualsCall() {
    this.getMethod() instanceof EqualsMethod
  }

  /**
   * A whitelist of method accesses allowed to perform
   * an incomparable-equals call.
   */
  predicate whitelisted() {
    // Allow tests and assertions to verify that `equals` methods return `false`.
    this.getParent*().(MethodAccess).getMethod().getName().matches("assert%") or
    this.getEnclosingStmt() instanceof AssertStmt
  }

  /** Whether the callee of this method access is `Object.equals`. */
  predicate invokesObjectEquals() {
    this.getMethod().getDeclaringType() instanceof TypeObject
  }

  /** Return the (static) type of the object on which `equals` is invoked. */
  RefType getReceiverType() {
    if exists(this.getQualifier()) then
      result = this.getQualifier().getType()
    else
      result = this.getEnclosingCallable().getDeclaringType()
  }

  /** Return the (static) type of the argument to `equals`. */
  RefType getArgumentType() {
    result = this.getArgument(0).getType()
  }
}

/*
 * Find calls to `equals` where the receiver and argument types are incomparable. 
 *
 * We check this in different ways, depending on whether the call invokes
 * the trivial `equals` implementation in `Object` or not.
 *
 * If it does, the two operands have to be of the same runtime type, so if their
 * static types have no intersection, the result is guaranteed to be false.
 *
 * If the `equals` method being invoked is not `Object.equals` but some overridden
 * version `A.equals`, we assume that `A.equals` requires the runtime type of its
 * operand to be a subtype of `A`. Hence, if `A` and the static type of the argument
 * have no intersection, the result is again guaranteed to be false.
 */
from EqualsCall ma, RefType recvtp, RefType argtp
where not ma.whitelisted() and
      (if ma.invokesObjectEquals()
       then recvtp = ma.getReceiverType()
       else recvtp = ma.getMethod().getDeclaringType()) and
      argtp = ma.getArgumentType() and
      not haveIntersection(recvtp, argtp)
select ma, "Call to equals() comparing incomparable types " + recvtp.getName() + " and " + argtp.getName() + "."
