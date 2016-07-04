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

import java
import semmle.code.java.comparison.Comparison
import semmle.code.java.dataflow.DefUse
import semmle.code.java.dataflow.Guards

/**
 * The kind of bound that is known to hold for some variable.
 */
library class BoundKind extends string {
	BoundKind() {
		this = "=" or
		this = "!=" or
		this = ">=" or
		this = "<="
	}
	
	predicate isEqual() {
		this = "="
	}
	
	predicate isNotEqual() {
		this = "!="
	}
	
	predicate isLower() {
		this = ">="
	}
	
	predicate isUpper() {
		this = "<="
	}
	
	predicate providesLowerBound() {
		isEqual() or isLower()
	}
	
	predicate providesUpperBound() {
		isEqual() or isUpper()
	}
}

/**
 * The information from `s1` implies that `test` always has the value `testIsTrue`.
 */
predicate uselessTest(ConditionNode s1, BinaryExpr test, boolean testIsTrue) {
	exists(LocalScopeVariable v, BinaryExpr cond, boolean condIsTrue, int k1, int k2, CompileTimeConstantExpr c1, CompileTimeConstantExpr c2 |
		s1 = cond and
		cond.hasOperands(v.getAnAccess(), c1) and c1.getIntValue() = k1 and
		test.hasOperands(v.getAnAccess(), c2) and c2.getIntValue() = k2 and
		controlsNodeWithSameVar(s1, condIsTrue, v, test) and
		v.getType() instanceof IntegralType and
		exists(BoundKind boundKind, int bound |
			// Simple range analysis. We infer a bound based on `cond` being
			// either true (`condIsTrue = true`) or false (`condIsTrue = false`).
			exists(EqualityTest condeq | cond = condeq and bound = k1 |
				condIsTrue = condeq.polarity() and boundKind.isEqual()
				or
				condIsTrue = condeq.polarity().booleanNot() and boundKind.isNotEqual()
			)
			or
			exists(ComparisonExpr comp | comp = cond |
				comp.getLesser() = v.getAnAccess() and
					(condIsTrue = true and boundKind.isUpper() and (if comp.isStrict() then bound = k1-1 else bound = k1)
					or
					condIsTrue = false and boundKind.isLower() and (if comp.isStrict() then bound = k1 else bound = k1+1))
				or
				comp.getGreater() = v.getAnAccess() and
					(condIsTrue = true and boundKind.isLower() and (if comp.isStrict() then bound = k1+1 else bound = k1)
					or
					condIsTrue = false and boundKind.isUpper() and (if comp.isStrict() then bound = k1 else bound = k1-1))
			)
		|
			// Given the bound we check if the `test` is either
			// always true (`testIsTrue = true`) or always false (`testIsTrue = false`).
			exists(EqualityTest testeq, boolean pol | testeq = test and pol = testeq.polarity() |
				(boundKind.providesLowerBound() and k2 < bound or
				 boundKind.providesUpperBound() and bound < k2 or
				 boundKind.isNotEqual() and k2 = bound) and testIsTrue = pol.booleanNot()
				or
				boundKind.isEqual() and k2 = bound and testIsTrue = pol
			)
			or
			exists(ComparisonExpr comp | comp = test |
				comp.getLesser() = v.getAnAccess() and
					(boundKind.providesLowerBound() and testIsTrue = false and (k2 < bound or k2 = bound and comp.isStrict())
					or
					boundKind.providesUpperBound() and testIsTrue = true and (bound < k2 or bound = k2 and not comp.isStrict()))
				or
				comp.getGreater() = v.getAnAccess() and
					(boundKind.providesLowerBound() and testIsTrue = true and (k2 < bound or k2 = bound and not comp.isStrict())
					or
					boundKind.providesUpperBound() and testIsTrue = false and (bound < k2 or bound = k2 and comp.isStrict()))
			)
		)
	)
}
