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

/**
 * Provides support for conversion contexts, in which an expression is converted 
 * (implicitly or explicitly) to a different type.
 * 
 * See the Java Language Specification, Section 5, for details.
 */
import java
import semmle.code.java.arithmetic.Overflow

/**
 * A expression where an implicit conversion can occur.
 * 
 * See the Java Language Specification, Section 5.
 */
abstract class ConversionSite extends Expr {
	/**
	 * The type that is converted to.
	 */
	abstract Type getConversionTarget();

	/**
	 * The type that is converted from.
	 */
	Type getConversionSource() {
		result = this.getType()
	}
	
	/**
	 * Whether this conversion site actually induces a conversion.
	 */
	predicate isTrivial() {
		getConversionTarget() = getConversionSource()
	}
	
	/**
	 * Whether this conversion is implicit.
	 */
	predicate isImplicit() {
		any()
	}

	abstract string kind();
}

/**
 * An assignment conversion. For example, `x += b` converts `b`
 * to be of the type of `x`.
 * 
 * See the Java Language Specification, Section 5.2.
 */
class AssignmentConversionContext extends ConversionSite {
	Variable v;
	AssignmentConversionContext() {
		this = v.getAnAssignedValue() or 
		exists(Assignment a | a.getDest().getProperExpr() = v.getAnAccess() and this = a.getSource())
	}
	
	Type getConversionTarget() {
		result = v.getType()
	}
	
	string kind() {
		result = "assignment context"
	}
}

/**
 * An return conversion. For example, `return b` converts `b`
 * to be of the return type of the enclosing callable.
 * 
 * Note that the Java Language Specification handles these as
 * assignment conversions (section 5.2), but for clarity we split them out here.
 */
class ReturnConversionSite extends ConversionSite {
	ReturnStmt r;
	ReturnConversionSite() {
		this = r.getResult()
	}
	
	Type getConversionTarget() {
		result = r.getEnclosingCallable().getReturnType()
	}
	string kind() {
		result = "return context"
	}
}

/**
 * An invocation conversion. For example `f(b)` converts `b` to 
 * have the type of the corresponding parameter of `f`.
 * 
 * See the Java Language Specification, Section 5.3.
 */
class InvocationConversionContext extends ConversionSite {
	Call c;
	int index;
	InvocationConversionContext() {
		this = c.getArgument(index)
	}
	
	Type getConversionTarget() {
		result = c.getCallee().getParameter(index).getType()
	}
	
	string kind() {
		result = "invocation context"
	}
}

/**
 * A string conversion. For example `a + b`, where `a` is a
 * `String`, converts `b` to have type `String`.
 * 
 * See the Java Language Specification, Section 5.4.
 */
class StringConversionContext extends ConversionSite {
	AddExpr a;
	StringConversionContext() {
		a.getAnOperand() = this and
		not this.getType() instanceof TypeString and
		a.getAnOperand().getType() instanceof TypeString
	}
	
	Type getConversionTarget() {
		result instanceof TypeString
	}
	
	string kind() {
		result = "string context"
	}
}

class CastConversionContext extends ConversionSite {
	CastExpr c;
	CastConversionContext() {
		this = c.getExpr()
	}
	
	Type getConversionTarget() {
		result = c.getType()
	}
	
	predicate isImplicit() {
		none()
	}
	
	string kind() {
		result = "cast context"
	}
}

/**
 * A numeric conversion. For example, `a * b` converts `a` and
 * `b` to have an appropriate numeric type.
 * 
 * See the Java Language Specification, Section 5.4.
 */
class NumericConversionContext extends ConversionSite {
	ArithExpr e;
	NumericConversionContext() {
		this = e.getAnOperand()
	}
	
	Type getConversionTarget() {
		result = e.getType()
	}
	
	string kind() {
		result = "numeric context"
	}
	
}