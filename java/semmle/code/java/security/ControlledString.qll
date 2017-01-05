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

/*
 * Controlled strings are the opposite of tainted strings.
 * There is positive evidence that they are fully controlled by
 * the program source code.
 */

import semmle.code.java.Expr
import semmle.code.java.security.Validation

/**
 * A `toString()` method on a boxed type. These never return special characters.
 */
private predicate boxedToString(Method method) {
  method.getDeclaringType() instanceof BoxedType
  and method.getName() = "toString"
}

/**
 * A static analysis of strings that end in a single quote. When such strings are concatenated
 * with another string, it suggests the programmer believes that code needed quoting. However,
 * it is better to use a prepared query than to just put single quotes around the string.
 */
predicate endsInQuote(Expr expr) {
  exists (string str | str = ((StringLiteral) expr).getLiteral().replaceAll("\"", "") |
    str.matches("%'"))
  or exists (Variable var | expr = var.getAnAccess() | endsInQuote(var.getAnAssignedValue()))
  or endsInQuote(expr.(AddExpr).getRightOperand())
}

/** The given expression is controlled if the other expression is controlled. */
private
predicate controlledStringProp(Expr src, Expr dest) {
  // Propagation through variables.
  exists (Variable var | var.getAnAccess() = dest | src = var.getAnAssignedValue())
  // Propagation through method parameters.
  or exists (Parameter param, MethodAccess call, int i |
    src = call.getArgument(i)
    and param = call.getMethod().getParameter(i)
    and dest = param.getAnAccess()
  )
  // Concatenation of safe strings.
  or exists (AddExpr concat | concat = dest | src = concat.getAnOperand())
  // `toString()` on a safe string is safe.
  or exists (MethodAccess toStringCall, Method toString |
    src = toStringCall.getQualifier()
    and toString = toStringCall.getMethod()
    and toString.hasName("toString")
    and toString.getNumberOfParameters() = 0
    and dest = toStringCall
  )
}

/** Expressions that have a small number of inflows from `controlledStringProp`. */
private
predicate modestControlledStringInflow(Expr dest) {
  strictcount(Expr src | controlledStringProp(src, dest)) < 10
}

/**
 * A limited version of `controlledStringProp` that ignores destinations that are written a
 * very high number of times.
 */
private
predicate controlledStringLimitedProp(Expr src, Expr dest) {
  controlledStringProp(src, dest)
  and modestControlledStringInflow(dest)
}

/**
 * Strings that are known to not include any special characters, due to being fully
 * controlled by the programmer.
 */
cached
predicate controlledString(Expr expr) {
  (expr instanceof StringLiteral
  or expr instanceof NullLiteral
  or ((VarAccess) expr).getVariable() instanceof EnumConstant
  or expr.getType() instanceof PrimitiveType
  or expr.getType() instanceof BoxedType
  or exists (Method method | method = ((MethodAccess) expr).getMethod() |
    method instanceof ClassNameMethod
    or method instanceof ClassSimpleNameMethod
    or boxedToString(method)
  )
  or exists (ValidatedVariable var | var.getAnAccess() = expr)
  or forex(Expr other | controlledStringLimitedProp(other, expr) | controlledString(other)))
  and not expr instanceof TypeAccess
}
