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

import Locations
import Stmt
import Variables
import AST
import BasicBlocks

/** A function as defined either by a function declaration or a function expression. */
class Function extends @function, Parameterized, StmtContainer {
  /** Get the i-th parameter of this function. */
	Parameter getParameter(int i) {
		result = getChildExpr(i)
	}

	/** Get a parameter of this function. */
	Parameter getAParameter() {
	  exists (int idx | result = getParameter(idx))
	}

	/** Get the parameter with the given name. */
	SimpleParameter getParameterByName(string name) {
	  result = getAParameter() and
	  result.getName() = name
	}
	
	/** Get the identifier specifying the name of this function, if any. */
	VarDecl getId() {
	 result = getChildExpr(-1)
	}
  
  /** Get the name of this function. */
  string getName() {
    result = getId().getName()
  }
	
	/** Get the variable holding this function. */
	Variable getVariable() {
	  result = getId().getVariable()
	}
	
	/** Get the scope induced by this function. */ 
	Scope getScope() {
		scopenodes(this, result)
	}
	
	/**
	 * Get the 'arguments' object of this function. If the function declares
	 * a parameter or local variable named 'arguments', it does not have an 'arguments'
	 * object.
	 */
	ArgumentsObject getArgumentsObject() {
	  result.getFunction() = this
	}
	
	/** Does the body of this function refer to the function's 'arguments' object? */
	predicate usesArgumentsObject() {
	  exists (getArgumentsObject().getAnAccess())
	}
	
	/** Does this function declare a parameter or local variable named 'arguments'? */
	predicate shadowsArgumentsObject() {
	  not exists(getArgumentsObject())
	}
	
	/** Get the statement enclosing this function. */
	Stmt getEnclosingStmt() {
	  none()
	}
	
	/** Get the body of this function. */
	ExprOrStmt getBody() {
	  result = getChild(-2)
	}

	/** Get the i-th statement in the body of this function. */
	Stmt getBodyStmt(int i) {
	  result = getBody().(BlockStmt).getStmt(i)
	}

	/** Get some statement in the body of this function. */
	Stmt getABodyStmt() {
	  result = getBodyStmt(_)
	}

	/** Get the number of statements in the body of this function. */
	int getNumBodyStmt() {
	  result = count(getABodyStmt())
	}

	/** Is this function a generator function? */
	predicate isGenerator() {
	  isGenerator(this)
	}

	/** Is the last parameter of this function a rest parameter? */
	predicate hasRestParameter() {
	  hasRestParameter(this)
	}

	/**
	 * The last token of this function's parameter list, not including
	 * the closing parenthesis (if any).
	 */
	private Token lastTokenOfParameterList() {
	  // if there are any parameters, it's the last token of the last parameter
	  exists (Parameter lastParam | lastParam = getParameter(getNumParameter()-1) |
	    result = lastParam.getDefault().getLastToken() or
	    not exists(lastParam.getDefault()) and result = lastParam.getLastToken()
	  )
	  or
	  // otherwise we have an empty parameter list `()`, and
	  // we want to return the opening parenthesis
	  not exists(getAParameter()) and
	  (
	    // if the function has a name, the opening parenthesis comes right after it
	    result = getId().getLastToken().getNextToken() or
	    // otherwise this must be an arrow function with no parameters, so the opening
	    // parenthesis is the very first token of the function
	    not exists(getId()) and result = getFirstToken()
	  )
	}

	/** Does the parameter list of this function have a trailing comma? */
	predicate hasTrailingComma() {
	  lastTokenOfParameterList().getNextToken().getValue() = ","
	}

	/** Is this function an asynchronous function? */
	predicate isAsync() {
	  isAsync(this)
	}

	/** Get the enclosing function or toplevel of this function. */
	StmtContainer getEnclosingContainer() {
	  result = getEnclosingStmt().getContainer()
	}

  /** Get the number of lines in this function. */
  int getNumberOfLines() {
    numlines(this, result, _, _)
  }

  /** Get the number of lines containing code in this function. */
  int getNumberOfLinesOfCode() {
    numlines(this, _, result, _)
  }

  /** Get the number of lines containing comments in this function. */
  int getNumberOfLinesOfComments() {
    numlines(this, _, _, result)
  }

  /** Compute the cyclomatic complexity of this function. */
  int getCyclomaticComplexity() {
    result = sum (Expr nd | nd.getContainer() = this and nd.isBranch() | strictcount(nd.getASuccessor()) - 1)
           + 2
  }

	/** Get the first basic block in this function. */
	BasicBlock getEntryBB() {
	  result = getEntry()
	}

	/** Get the JSDoc documentation for this function, if any. */
	JSDoc getDocumentation() {
	  none()
	}

	predicate isStrict() {
	  exists (StrictModeDecl smd | this = smd.getContainer()) or
	  StmtContainer.super.isStrict()
	}
	
	/** Get a return statement in the body of the functions, if any. */
	ReturnStmt getAReturnStmt() {
	  result.getContainer() = this
	}
	
	/** Get an expression that could be returned by the function, if any. */
	Expr getAReturnedExpr() {
	  result = getBody() or
	  result = getAReturnStmt().getExpr()
	}
}