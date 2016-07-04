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
 * A library for nullness analysis.
 */

import default

/** An expression that may be `null`. */
private Expr nullExpr() {
	result instanceof NullLiteral or
	((ParExpr) result).getExpr() = nullExpr() or
	((ConditionalExpr) result).getTrueExpr() = nullExpr() or
	((ConditionalExpr) result).getFalseExpr() = nullExpr()
}

/** An expression that may be non-`null`. */
private Expr nonNullExpr() {
	not (result instanceof NullLiteral or result instanceof ConditionalExpr or result instanceof ParExpr) or
	((ParExpr) result).getExpr() = nonNullExpr() or
	((ConditionalExpr) result).getTrueExpr() = nonNullExpr() or
	((ConditionalExpr) result).getFalseExpr() = nonNullExpr()
}

/** An assignment to the specified local variable that may be `null`. */
private AssignExpr nullSet(LocalVariableDecl var) {
	var.getAnAccess() = result.getDest() and
	result.getSource() = nullExpr()
}

/** An assignment to the specified local variable that may be non-`null`. */
private AssignExpr nonNullSet(LocalVariableDecl var) {
	var.getAnAccess() = result.getDest() and
	result.getSource() = nonNullExpr()
}

/**
 * An expression that accesses the specified local variable
 * such that it will result in an NPE if the variable evaluates to `null`.
 */
private Expr nonNullUse(LocalVariableDecl var) {
	result = nonNullAccess(var.getAnAccess())
}

/**
 * An expression that will result in an NPE if the specified local variable evaluates to `null`.
 */
private Expr nonNullAccess(VarAccess access) {
	((FieldAccess) result).getQualifier() = access or
	((MethodAccess) result).getQualifier() = access or
	((ArrayAccess) result).getArray() = access
}

/**
 * A local variable declaration expression that may
 * initialize the specified local variable with `null`.
 */
private LocalVariableDeclExpr initialNull(LocalVariableDecl var) {
	result.getVariable() = var and
	result.getInit() = nullExpr()
}

/**
 * A local variable declaration expression that may
 * initialize the specified local variable with a non-`null` expression.
 */
private LocalVariableDeclExpr initialNonNull(LocalVariableDecl var) {
	result.getVariable() = var and
	result.getInit() = nonNullExpr()
}

/**
 * An argument of a method access to a method with the specified name,
 * where the corresponding parameter has type `Object`.
 */
private Expr getAnArgumentWithTypeObject(string methodname) {
	exists(Method method, int i |
		result = method.getAReference().getArgument(i) and
		method.getParameter(i).getType() instanceof TypeObject and
		method.hasName(methodname)
	)
}

/**
 * A statement that either asserts that the specified local variable is `null` or
 * that may assign `null` to the specified local variable.
 */
private Stmt nullDef(LocalVariableDecl var) {
	result = nullDefExpr(var).getEnclosingStmt() or
	exists(Expr expr | result = expr.getEnclosingStmt() and
		sameValue(expr, var.getAnAccess()) and expr = getAnArgumentWithTypeObject("assertNull")) or
	exists(Expr expr, MethodAccess call, Callable method | result = expr.getEnclosingStmt() and expr = nullTest(var) and
		expr = call.getAnArgument() and call.getCallee() = method and method.hasName("assertTrue")) or
	exists(Expr expr, MethodAccess call, Callable method | result = expr.getEnclosingStmt() and expr = failureIsNullTest(var) and
		expr = call.getAnArgument() and call.getCallee() = method and method.hasName("assertFalse"))
}

/**
 * An expression that may initialize the specified local variable with `null` or assign `null` to it.
 */
private Expr nullDefExpr(LocalVariableDecl var) {
	nullSet(var) = result or
	initialNull(var) = result
}

/**
 * A statement that either asserts that the specified local variable is non-`null`,
 * dereferences it, or may assign a non-`null` expression to it.
 */
private Stmt nonNullDef(LocalVariableDecl var) {
	result = nonNullDefExpr(var).getEnclosingStmt() or
	exists(SynchronizedStmt stmt | stmt = result and stmt.getExpr() = var.getAnAccess()) or
	exists(EnhancedForStmt stmt | stmt = result and stmt.getVariable().getVariable() = var) or
	exists(Expr expr | result = expr.getEnclosingStmt() and sameValue(expr, var.getAnAccess()) and
		(expr = getAnArgumentWithTypeObject("assertNotNull") or expr = getAnArgumentWithTypeObject("assertNonNull"))) or
	exists(Expr expr, MethodAccess call, Callable method | result = expr.getEnclosingStmt() and expr = nonNullTest(var) and
		expr = call.getAnArgument() and call.getCallee() = method and method.hasName("assertTrue")) or
	exists(Expr expr, MethodAccess call, Callable method | result = expr.getEnclosingStmt() and expr = failureIsNonNullTest(var) and
		expr = call.getAnArgument() and call.getCallee() = method and method.hasName("assertFalse"))
}

/**
 * An expression that either initializes the specified local variable with a non-`null` expression,
 * assigns a non-`null` expression to it, or accesses it in a way that would cause an NPE if it were `null`.
 */
private Expr nonNullDefExpr(LocalVariableDecl var) {
	nonNullSet(var) = result or
	nonNullUse(var)= result or
	initialNonNull(var) = result
}

/** A logical OR expression in which the specified expression is a (possibly nested) operand. */
private OrLogicalExpr orParent(Expr e) {
	e = result.getAnOperand()
	or
	exists(OrLogicalExpr orexpr | result = orParent(orexpr) and e = orexpr.getAnOperand())
}

/** A logical AND expression in which the specified expression is a (possibly nested) operand. */
private AndLogicalExpr andParent(Expr e) {
	e = result.getAnOperand()
	or
	exists(AndLogicalExpr andexpr | result = andParent(andexpr) and e = andexpr.getAnOperand())
}

/**
 * Whether a variable access has the "same value" as an expression:
 *
 * - the variable access is equal to the expression, or
 * - the expression is an assignment and the variable access is its left-hand side, or
 * - the expression is an assignment and the variable access has the same value as its right-hand side.
 */
private predicate sameValue(Expr expr, VarAccess access) {
	access = expr or
	access = ((AssignExpr)expr).getDest() or
	sameValue(((AssignExpr)expr).getSource(), access) or
	sameValue(((ParExpr) expr).getExpr(), access)
}

/** An `instanceof` expression in which the left-hand side is an access to the specified variable. */
private Expr instanceOfTest(LocalVariableDecl var) {
	exists(InstanceOfExpr e | result = e and
		sameValue(e.getExpr() , var.getAnAccess()))
}

/**
 * A method access to a method with the specified name, a single argument, and return type `boolean`,
 * where the only argument is an access to the specified local variable.
 */
private Expr testCall(string name, LocalVariableDecl var) {
	exists(Callable callee, MethodAccess call |
		callee = call.getCallee() and
		callee.getNumberOfParameters() = 1 and
		sameValue(call.getAnArgument() , var.getAnAccess()) and
		callee.getType().hasName("boolean") and
		callee.getName() = name and
		call = result
	)
}

/**
 * An expression performing a `null` check on the specified local variable,
 *
 * - either via a reference equality test with `null`, or
 * - by passing it as an argument to an `isNull` method.
 */
private Expr directNullTest(LocalVariableDecl var) {
	exists(EQExpr eq | result = eq and
		sameValue(eq.getAnOperand() , var.getAnAccess()) 
		and eq.getAnOperand() instanceof NullLiteral)
	or result = testCall("isNull", var)
	or // seems redundant, because all methods that use this method also peel ParExp
	   // However, removing this line causes an increase of memory usage
	((ParExpr) result).getExpr() = directNullTest(var)
}

/**
 * An expression performing a non-`null` check on the specified local variable,
 *
 * - either via an inequality test with `null`, or
 * - by passing it as an argument to an `isNotNull` or `isNonNull` method.
 */
private Expr directNonNullTest(LocalVariableDecl var) {
	exists(NEExpr ne | result = ne and
		sameValue(ne.getAnOperand() , var.getAnAccess()) 
		and ne.getAnOperand() instanceof NullLiteral)
	or result = testCall("isNotNull", var) or result = testCall("isNonNull", var) 
	or // seems redundant, because all methods that use this method also peel ParExp
	   // However, removing this line causes an increase of memory usage
	((ParExpr) result).getExpr() = directNonNullTest(var)
}

/**
 * A `null` test in a _positive_ position for the specified variable.
 */
private Expr nullTest(LocalVariableDecl var) {
	directNullTest(var) = result
	or
	((ParExpr) result).getExpr() = nullTest(var)
	or
	exists(LogNotExpr notexpr | result = notexpr and
		notexpr.getExpr() = failureIsNullTest(var))
	or
	result = andParent(nullTest(var))
	or
	exists(OrLogicalExpr orexpr | result = orexpr and
		orexpr.getLeftOperand() = nullTest(var) and
		orexpr.getRightOperand() = nullTest(var))
}

/**
 * A non-`null` test in a _positive_ position for the specified variable.
 */
private Expr nonNullTest(LocalVariableDecl var) {
	directNonNullTest(var) = result
	or
	instanceOfTest(var) = result
	or
	((ParExpr) result).getExpr() = nonNullTest(var)
	or
	exists(LogNotExpr notexpr | result = notexpr and
		notexpr.getExpr() = failureIsNonNullTest(var))
	or
	result = andParent(nonNullTest(var))
	or
	exists(OrLogicalExpr orexpr | result = orexpr and
		orexpr.getLeftOperand() = nonNullTest(var) and
		orexpr.getRightOperand() = nonNullTest(var))
}

/**
 * A non-`null` test in a _negative_ position for the specified variable.
 */
private Expr failureIsNullTest(LocalVariableDecl var) {
	directNonNullTest(var) = result
	or
	((ParExpr) result).getExpr() = failureIsNullTest(var)
	or
	exists(LogNotExpr notexpr | result = notexpr and
		notexpr.getExpr() = failureIsNonNullTest(var))
	or
	result = orParent(failureIsNullTest(var))
	or
	exists(AndLogicalExpr andexpr | result = andexpr and
		andexpr.getLeftOperand() = failureIsNullTest(var) and
		andexpr.getRightOperand() = failureIsNullTest(var))
}

/**
 * A `null` test in a _negative_ position for the specified variable.
 */
private Expr failureIsNonNullTest(LocalVariableDecl var) {
	directNullTest(var) = result
	or
	((ParExpr) result).getExpr() = failureIsNonNullTest(var)
	or
	exists(LogNotExpr notexpr | result = notexpr and
		notexpr.getExpr() = failureIsNullTest(var))
	or
	result = orParent(directNullTest(var))
	or
	exists(AndLogicalExpr andexpr | result = andexpr and
		andexpr.getLeftOperand() = failureIsNonNullTest(var) and
		andexpr.getRightOperand() = failureIsNonNullTest(var))
}

/**
 * An immediate successor statement of the specified conditional statement where
 * the condition implies that the specified local variable is `null`.
 */
private Stmt nullBranchKill(LocalVariableDecl var, ConditionalStmt condStmt) {
	(condStmt.getCondition() = nullTest(var) and
		result = condStmt.getTrueSuccessor())
	or
	(condStmt.getCondition() = failureIsNullTest(var) and
		result = condStmt.getFalseSuccessor())
}

/**
 * An immediate successor statement of the specified conditional statement where
 * the condition implies that the specified local variable is non-`null`.
 */
private Stmt nonNullBranchKill(LocalVariableDecl var, ConditionalStmt condStmt) {
	(condStmt.getCondition() = nonNullTest(var) and
		result = condStmt.getTrueSuccessor())
	or
	(condStmt.getCondition() = failureIsNonNullTest(var) and
		result = condStmt.getFalseSuccessor())
}

/** A statement where the specified local variable may be `null`. */
Stmt maybeNullStmt(LocalVariableDecl var) {
	exists(Stmt nullDef | nullDef = nullDef(var) |
		result = nullDef.getASuccessor() and not result = nonNullBranchKill(var, nullDef)
	)
	or
	exists(Stmt mid |
		mid = maybeNullStmt(var) and
		not mid = nonNullDef(var) and
		mid.getASuccessor() = result and
		not result = nonNullBranchKill(var, mid)
	)
}

/** A statement where the specified local variable may be non-`null`. */
Stmt maybeNonNullStmt(LocalVariableDecl var) {
	exists(Stmt nonNullDef| nonNullDef = nonNullDef(var) | 
		result = nonNullDef.getASuccessor() and not result = nullBranchKill(var, nonNullDef)
	)
	or
	exists(Stmt mid |
		mid = maybeNonNullStmt(var) and
		not mid = nullDef(var) and
		mid.getASuccessor() = result and
		not result = nullBranchKill(var, mid)
	)
}

/**
 * An expression whose evaluation may be guarded by
 * a non-`null` check for the specified variable.
 */
private Expr nullGuarded(LocalVariableDecl var) {
	exists(OrLogicalExpr guard |
		(guard.getLeftOperand() = failureIsNonNullTest(var) or
		 guard.getLeftOperand() = nonNullDefExpr(var).getParent*()) and
		result = guard.getRightOperand())
	or
	exists(AndLogicalExpr guard |
		(guard.getLeftOperand() = nonNullTest(var) or
		 guard.getLeftOperand() = nonNullDefExpr(var).getParent*()) and
		result = guard.getRightOperand())
	or
	exists(ConditionalExpr cond |
		(cond.getCondition() = failureIsNonNullTest(var) or
		 cond.getCondition() = nonNullDefExpr(var).getParent*()) and
		result = cond.getFalseExpr())
	or
	exists(ConditionalExpr cond |
		(cond.getCondition() = nonNullTest(var) or
		 cond.getCondition() = nonNullDefExpr(var).getParent*()) and
		result = cond.getTrueExpr())
	or
	result.getParent() = nullGuarded(var)
}

/** A variable access that must be non-`null` to avoid an NPE. */
private predicate dereferenced(VarAccess access) {
	exists(nonNullAccess(access)) or
	exists(EnhancedForStmt stmt | stmt.getExpr() = access) or
	exists(SynchronizedStmt stmt | stmt.getExpr() = access)
}

/**
 * A dereferenced access to the specified local variable that
 *
 * - does not occur within a `null`-guarded expression, but
 * - occurs within a statement where the variable may be `null`.
 */
VarAccess unguardedMaybeNullDereference(LocalVariableDecl var) {
	var.getAnAccess() = result and
	maybeNullStmt(var) = result.getEnclosingStmt() and
	dereferenced(result) and
	not result = nullGuarded(var)
}

/**
 * A dereferenced access to the specified local variable that
 *
 * - does not occur within a `null`-guarded expression, but
 * - occurs within a statement where the variable may be `null`, and
 * - does not occur within a statement where the variable may be non-`null`.
 */
VarAccess unguardedNullDereference(LocalVariableDecl var) {
	unguardedMaybeNullDereference(var) = result and
	not maybeNonNullStmt(var) = result.getEnclosingStmt()
}
