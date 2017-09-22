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
 * Provides predicates that specify information about
 * the behavior of the program being analyzed.
 *
 * By default they contain reasonable defaults for all projects, but by
 * modifying this file, you can customize the standard Semmle analyses
 * to give better results for your project.
 */

import cpp
import semmle.code.cpp.controlflow.Dataflow
import semmle.code.cpp.commons.Synchronization
private import semmle.code.cpp.controlflow.internal.ConstantExprs

/**
 * Holds if we wish to override the "may return NULL" inference for this
 * call. If this holds, then rather than trying to infer whether this
 * call might return NULL, we will instead test whether `returnsNull`
 * holds for it.
 *
 * By default, this handles the `Xstrdup` function used by the CVS
 * project.
 */
predicate overrideReturnsNull(Call call) {
  // Used in CVS:
  call.(FunctionCall).getTarget().hasQualifiedName("Xstrdup")
}

/**
 * Holds if this call may return NULL. This is only used if
 * `overrideReturnsNull` holds for the call.
 *
 * By default, this handles the `Xstrdup` function used by the CVS
 * project.
 */
predicate returnsNull(Call call) {
  // Used in CVS:
  call.(FunctionCall).getTarget().hasQualifiedName("Xstrdup") and
  nullValue(call.getArgument(0))
}

/**
 * Holds if a call to this function will never return.
 *
 * By default, this holds for `exit`, `_exit`, `abort`, `__assert_fail`,
 * `longjmp`, `error`, `__builtin_unreachable` and any function with a
 * `noreturn` attribute.
 */
predicate exits(Function f) {
  f.getAnAttribute().hasName("noreturn") or
  exists(string name | f.getQualifiedName() = name |
    name = "exit" or
    name = "_exit" or
    name = "abort" or
    name = "__assert_fail" or
    name = "longjmp" or
    name = "error" or
    name = "__builtin_unreachable"
  )
}

/**
 * Holds if evaluating expression `e` will never return, or can be assumed
 * to never return.  For example:
 * ```
 *   __assume(0);
 * ```
 * (note that in this case if the hint is wrong and the expression is reached at
 * runtime, the program's behaviour is undefined)
 */
predicate exprExits(Expr e) {
  e.(AssumeExpr).getChild(0).(CompileTimeConstantInt).getIntValue() = 0
}

/**
 * Holds if function `f` should always have its return value checked.
 *
 * By default holds only for `fgets`.
 */
predicate alwaysCheckReturnValue(Function f) {
  f.hasQualifiedName("fgets")
}

/**
 * Holds if it is reasonable to ignore the return value of function
 * call `fc`.
 *
 * By default holds for calls to `select` where the first argument is
 * `0` (commonly used as a way of sleeping), and any call inside a
 * macro expansion.
 */
predicate okToIgnoreReturnValue(FunctionCall fc) {
  fc.isInMacroExpansion()
  or
  // common way of sleeping using select:
  (fc.getTarget().hasQualifiedName("select") and
   fc.getArgument(0).getValue() = "0")
}

/**
 * A type that acts as a mutex.
 */
class CustomMutexType extends MutexType {
  CustomMutexType() {
    none()
  }

  /**
   * Holds if `fc` is a call that always locks mutex `arg`
   * of this type.
   */
  predicate mustlockAccess(FunctionCall fc, Expr arg) {
    none()
  }

  /**
   * Holds if `fc` is a call that tries to lock mutex `arg`
   * of this type, but may return without success.
   */ 
  predicate trylockAccess(FunctionCall fc, Expr arg) {
    none()
  }

  /**
   * Holds if `fc` is a call that unlocks mutex `arg`
   * of this type.
   */ 
  predicate unlockAccess(FunctionCall fc, Expr arg) {
    none()
  }
}