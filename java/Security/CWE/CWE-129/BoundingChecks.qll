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
 * A library for determining upper and lower bounds on a value determined by bounding checks that
 * have been made on dominant paths.
 */

import java

import semmle.code.java.controlflow.Dominance

/**
 * If condition is a conjuctive term, return the conjunctions, otherwise just return the condition.
 */
Expr getAConjunctiveTerm(Expr condition) {
	if condition instanceof AndLogicalExpr then
		result = getAConjunctiveTerm(condition.(AndLogicalExpr).getAnOperand())
	else
		result = condition
}

/**
 * Whether `b` follows `a` in a series of conjunctions. Short-circuit evaluation should mean that
 * `b` is evaluated only if `a` is true.
 */
predicate conjunctiveSuccessor(Expr a, Expr b) {
	exists(AndLogicalExpr ale |
		getAConjunctiveTerm(ale.getLeftOperand()) = a and
		getAConjunctiveTerm(ale.getRightOperand()) = b
	)
}

/**
 * Whether the given `ComparisonExpr` is thought to be true when `VarAccess` is accessed.
 */
predicate conditionHolds(ComparisonExpr ce, VarAccess va) {
	conjunctiveSuccessor(ce, va.getParent*()) or
	exists(IfStmt ifStmt |
		getAConjunctiveTerm(ifStmt.getCondition()) = ce and
		/*
		 * We use dominance to consider if this condition holds prior to the access of the variable. This is
		 * a limited check - it might not be sufficient if the variable is changed in the meantime.
		 */
		dominates(ifStmt.getThen(), va.getEnclosingStmt())
	) or
	exists(ConditionalExpr conditionalExpr |
		getAConjunctiveTerm(conditionalExpr.getCondition()) = ce and
		conditionalExpr.getTrueExpr() = va.getParent*()
	)
}

/**
 * Determine an inclusive lower-bound - if possible - for the value accessed by the given `VarAccess`,
 * based upon the conditionals that hold at the point the variable is accessed.
 */
int lowerBound(VarAccess va) {
	exists(ComparisonExpr greaterThanValue |
		// This condition should hold when the variable is later accessed.
		conditionHolds(greaterThanValue, va) |
		greaterThanValue.getGreater() = va.getVariable().getAnAccess() and
		if greaterThanValue.isStrict() then
			// value > i, so value has a lower bound of i + 1
			result = greaterThanValue.getLesser().(CompileTimeConstantExpr).getIntValue() + 1
		else
			// value >= i, so value has a lower bound of i
			result = greaterThanValue.getLesser().(CompileTimeConstantExpr).getIntValue()
	)
}

/**
 * Whether the index expression is a `VarAccess`, where the variable has been confirmed to be less
 * than the length.
 */
predicate lessthanLength(ArrayAccess a) {
	exists(ComparisonExpr lessThanLength, VarAccess va |
		va = a.getIndexExpr() and
		conditionHolds(lessThanLength, va) |
		lessThanLength.getGreater().(FieldAccess).getQualifier() = arrayReference(a) and
		lessThanLength.getGreater().(FieldAccess).getField().hasName("length") and
		lessThanLength.getLesser() = va.getVariable().getAnAccess() and
		lessThanLength.isStrict()
	)
}

/**
 * Return all other references to the array accessed in the `ArrayAccess`.
 */
Expr arrayReference(ArrayAccess arrayAccess) {
	// Array is stored in a variable.
	result = arrayAccess.getArray().(VarAccess).getVariable().getAnAccess() or
	// Array is returned from a method.
	result.(MethodAccess).getCallee() = arrayAccess.getArray().(MethodAccess).getMethod()
}
