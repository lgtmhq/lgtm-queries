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

import semmle.javascript.Expr

/**
 * FunctionFlow and its subclasses implement data flow analysis for
 * function objects.
 */
abstract class FunctionFlow extends Expr {
	/**
	 * Get a source of the flow for which this expression is the target.
	 *
	 * Subclasses whose flow cannot be expressed in this way should override
	 * this predicate as 'none()', and override 'getAFunctionValue()' and
	 * 'isIncomplete' below.
	 */
	abstract Expr getAFlowSource();

	Function getAFunctionValue() {
		result = getAFlowSource().(FunctionFlow).getAFunctionValue()
	}
	
	/** Is our model of this flow incomplete? */
	predicate isIncomplete() {
		exists (Expr src | src = getAFlowSource() |
			not src instanceof FunctionFlow or
			src.(FunctionFlow).isIncomplete()
		)
	}
}

/** Identity flow: a function flows into the function expression defining it. */
class IdentityFunctionFlow extends FunctionFlow, FunctionExpr {
	Expr getAFlowSource() {
		result = this
	}

	Function getAFunctionValue() {
		result = this
	}
	
	predicate isIncomplete() {
		none()
	}
	
	// trivial overrides to keep the compiler happy
	Stmt getEnclosingStmt() { result = FunctionExpr.super.getEnclosingStmt() }
	predicate isImpure() { FunctionExpr.super.isImpure() }
	string toString() { result = FunctionExpr.super.toString() }
	JSDoc getDocumentation() { result = FunctionExpr.super.getDocumentation() }
}

/** Data flow through parentheses: anything that flows into e also flows into (e). */
class ParenFunctionFlow extends FunctionFlow, ParExpr {
	Expr getAFlowSource() {
		result = getExpression()
	}
	
	// trivial overrides to keep the compiler happy
	Expr stripParens() { result = ParExpr.super.stripParens() }
	predicate isImpure() { ParExpr.super.isImpure() }
	int getIntValue() { result = ParExpr.super.getIntValue() }
}

/** Data flow through assignments: anything that flows into rhs also flows into lhs = rhs. */
class AssignmentFunctionFlow extends FunctionFlow, AssignExpr {
	Expr getAFlowSource() {
	     result = getRhs()
	}

	CFGNode getFirstCFGNode() { result = AssignExpr.super.getFirstCFGNode() }
}

/** Data flow through conditional expressions: anything that flows into t or e also flows into c ? t : e. */
class ConditionalExprFunctionFlow extends FunctionFlow, ConditionalExpr {
	Expr getAFlowSource() {
	     result = getABranch()
	}
	
	// trivial override to keep the compiler happy
	predicate isImpure() { ConditionalExpr.super.isImpure() }
}

/** Data flow through short-circuiting expressions: anything that flows into a or b also flows into a || b.
 * Anything that flows into b also flows into a &amp;&amp; b. (Note that in the latter case we're not interested in
 * flows into a: a &amp;&amp; b only evaluates to a if a is falsy, which is never the case for functions.)
 */
class ShortCircuitExprFlow extends FunctionFlow, LogicalBinaryExpr {
	Expr getAFlowSource() {
		(getOperator() = "||" and result = getLeftOperand()) or
		result = getRightOperand()
	}
	
	// trivial override to keep the compiler happy
	predicate isImpure() { LogicalBinaryExpr.super.isImpure() }
  CFGNode getFirstCFGNode() { result = LogicalBinaryExpr.super.getFirstCFGNode() }
}

// helper predicate: check whether `v` may be assigned values through flows that we do not model
private predicate hasUntrackedFlow(Variable v) {
	exists (BindingPattern p |
		// we do not currently track flow through destructuring assignments...
		p instanceof ArrayPattern or p instanceof ObjectPattern or
		// ...or interprocedural flow
		p instanceof Parameter |
		v = p.getAVariable()
	)
}

/** Data flow through variables: anything that flows into the right hand side
 * of an assignment to a variable also flows into all its uses. */
class FunctionFlowThroughVariables extends FunctionFlow, VarAccess {
	Expr getAFlowSource() {
		result = getVariable().getAnAssignedValue()
	}

	Function getAFunctionValue() {
		result = FunctionFlow.super.getAFunctionValue() or
		// special case: function declarations are not expressions
		result.getVariable() = getVariable()
	}

	predicate isIncomplete() {
		hasUntrackedFlow(getVariable()) or
		FunctionFlow.super.isIncomplete()
	}
	
	// trivial overrides to keep the compiler happy
	predicate isImpure() { VarAccess.super.isImpure() }
}

/** arguments.callee is always a reference to the enclosing function */
class ArgumentsCalleeFlow extends FunctionFlow, PropAccess {
	ArgumentsCalleeFlow() {
		exists (ArgumentsObject arguments |
			getBase() = arguments.getAnAccess() and
			getPropertyName() = "callee"
		)
	}
	
	Expr getAFlowSource() {
		none()
	}
	
	Function getAFunctionValue() {
		result = getEnclosingFunction()
	}
	
	predicate isIncomplete() {
		none()
	}

  CFGNode getFirstCFGNode() { result = PropAccess.super.getFirstCFGNode() }
}
