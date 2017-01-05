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
import AST
import Variables
import Tokens

/** A statement. */
class Stmt extends @stmt, ExprOrStmt {
	/** Get the statement container (toplevel or function) to which this statement belongs. */
	StmtContainer getContainer() {
		stmtContainers(this, result)
	}

	/** Did this statement undergo implicit semicolon insertion? */
	predicate hasSemicolonInserted() {
	  isSubjectToSemicolonInsertion() and
	  getLastToken().getValue() != ";"
	}

	/** Does automatic semicolon insertion apply to this statement? */
	predicate isSubjectToSemicolonInsertion() {
	  none()
	}

	/**
	 * Get the kind of this statement, which is an integer
	 * value representing the statement's node type.
	 *
	 * _Note_: The mapping from node types to integers is considered an implementation detail
	 * and may change between versions of the extractor.
	 */
	int getKind() {
	  stmts(this, result, _, _, _)
	}


	/** Get the JSDoc comment associated with this statement. */
	JSDoc getDocumentation() {
	  result.getComment().getNextToken() = getFirstToken()
	}

	string toString() {
		stmts(this, _, _, _, result)
	}

	/**
	 * Get the statement that is parent of this statement in the AST, if any.
	 */
	Stmt getParentStmt() {
		this = result.getAChildStmt()
	}

	/**
	 * Is this statement lexically nested inside statement `outer`?
	 */
	predicate nestedIn(Stmt outer) {
		outer = getParentStmt+() or
		getContainer().(Expr).getEnclosingStmt().nestedIn(outer)
	}
}

/** A control statement, that is, is a loop, an if statement, a switch statement,
 * a with statement, a try statement, or a catch clause. */
abstract class ControlStmt extends Stmt {
  /** Get a statement controlled by this control statement. */
	abstract Stmt getAControlledStmt();
}

/** A loop, that is, is a while loop, a do-while loop, a for loop, or a for-in loop. */
abstract class LoopStmt extends ControlStmt {
  /** Get the body of this loop. */
	abstract Stmt getBody();
	
	/** Get the loop test of this loop. */
	abstract Expr getTest();
	
	Stmt getAControlledStmt() {
		result = getBody()
	}
}

/** An empty statement. */
class EmptyStmt extends @emptystmt, Stmt {}

/** A block of statements. */
class BlockStmt extends @blockstmt, Stmt {
  /** Get the i-th statement in this block. */
	Stmt getStmt(int i) {
		result = getChildStmt(i)
	}
	
	/** Get a statement in this block. */
	Stmt getAStmt() {
		result = getStmt(_)
	}
	
	/** Get the number of statements in this block. */
	int getNumStmt() {
		result = count(getAStmt())
	}
  
  /** Is this block a function body? */
  predicate isFunctionBody() {
    this.getParent() instanceof Function
  }
}

/** An expression statement. */
class ExprStmt extends @exprstmt, Stmt {
  /** Get the expression of this expression statement. */
	Expr getExpr() {
		result = getChildExpr(0)
	}

  predicate isSubjectToSemicolonInsertion() {
    not isDoubleColonMethod(_, _, _)
  }

  /**
   * Is this expression statement a JScript-style double colon method declaration?
   */
  predicate isDoubleColonMethod(Identifier interface, Identifier id, Function f) {
    // the parser converts double colon method declarations into assignments, but we
    // can consult token-level information to identify them
    exists (Assignment assgn, DotExpr dot, Token tk |
      assgn = getExpr() and
      dot = assgn.getLhs() and
      interface = dot.getBase() and
      // check if the interface name is followed by two colons
      tk = interface.getLastToken().getNextToken() and
      (tk.getValue() = ":" and  tk.getNextToken().getValue() = ":" or
       tk.getValue() = "::") and
      id = dot.getProperty() and
      f = assgn.getRhs()
    )
  }
}

/**
 * An expression statement wrapping a string literal (which may
 * be a directive).
 */
library class MaybeDirective extends ExprStmt {
  MaybeDirective() {
    getExpr() instanceof StringLiteral
  }

  /** The text of the string literal wrapped by this statement. */
  string getDirectiveText() {
    result = getExpr().(StringLiteral).getValue()
  }
}

/** A directive, such as a strict mode declaration. */
abstract class Directive extends MaybeDirective {
  /**
   * Get the scope to which this directive applies.
   *
   * DEPRECATED: Use `getContainer()` instead.
   */
  deprecated
  Scope getScope() {
    if this.getContainer() instanceof Function then
      result = ((Function)this.getContainer()).getScope()
    else
      result instanceof GlobalScope
  }
}

/** A strict mode declaration. */
class StrictModeDecl extends Directive {
  StrictModeDecl() { getDirectiveText() = "use strict" }
}

/** An asm.js directive. */
class ASMJSDirective extends Directive {
  ASMJSDirective() { getDirectiveText() = "use asm" }
}

/** A Babel directive. */
class BabelDirective extends Directive {
  BabelDirective() { getDirectiveText() = "use babel" }
}

/** A legacy 6to5 directive. */
class SixToFiveDirective extends Directive {
  SixToFiveDirective() { getDirectiveText() = "use 6to5" }
}

/** An if statement. */
class IfStmt extends @ifstmt, ControlStmt {
  /** Get the condition of this if statement. */
	Expr getCondition() {
		result = getChildExpr(0)
	}
	
	/** Get the 'then' branch of this if statement. */
	Stmt getThen() {
		result = getChildStmt(1)
	}
	
	/** Get the 'else' branch, if any, of this if statement. */
	Stmt getElse() {
		result = getChildStmt(2)
	}
	
	/** Get the 'if' token of this if statement. */
	KeywordToken getIfToken() {
		result = getFirstToken()
	}
	
	/** Get the 'else' token, if any, of this if statement. */
	KeywordToken getElseToken() {
		result = getThen().getLastToken().getNextToken() and
		result.getIndex() < getLastToken().getIndex()
	}
	
	Stmt getAControlledStmt() {
		result = getThen() or
		result = getElse()
	}
	
	/** Is this if statement an else-if of an outer if statement? */
	predicate isElseIf() {
		exists(IfStmt outer | outer.getElse() = this)
	}
}

/** A labeled statement. */
class LabeledStmt extends @labeledstmt, Stmt {
  /** Get the label of this statement. */
	string getLabel() {
		result = ((Identifier)getChildExpr(0)).getName()
	}
	
	/** Get the labeled statement of this statement. */
	Stmt getStmt() {
		result = getChildStmt(1)
	}
}

/**
 * A statement that disrupts structured control flow, that is, a
 * `continue` statement, a `break` statement,
 * a `throw` statement, or a `return` statement.
 */
abstract class JumpStmt extends Stmt {
  /**
   * Get the target of this jump.
   *
   * For break and continue statements, this predicate returns the statement
   * this statement breaks out of or continues with. For throw statements,
   * it returns the closest surrounding try statement in whose body the
   * throw statement occurs, or otherwise the enclosing statement container.
   * For return statements, this predicate returns the enclosing statement
   * container.
   *
   * Note that this predicate does not take `finally` clauses
   * into account, which may interrupt the jump.
   */
	abstract ASTNode getTarget();
}

/** A break or continue statement. */
abstract class BreakOrContinueStmt extends JumpStmt {
  /** Get the label this statement refers to, if any. */
  string getTargetLabel() {
    result = ((Identifier)getChildExpr(0)).getName()
  }
  
  /** Does this statement have an explicit target label? */
  predicate hasTargetLabel() {
    exists(getTargetLabel())
  }
  
  /** Get the statement this statement breaks out of or continues with. */
  Stmt getTarget() {
    jumpTargets(this, result)
  }

  predicate isSubjectToSemicolonInsertion() {
    any()
  }
}

/** A break statement. */
class BreakStmt extends @breakstmt, BreakOrContinueStmt {}

/** A continue statement. */
class ContinueStmt extends @continuestmt, BreakOrContinueStmt {}

/** A with statement. */
class WithStmt extends @withstmt, ControlStmt {
  /** Get the controlling expression if this with statement. */
	Expr getExpr() {
		result = getChildExpr(0)
	}
	
	/** Get the body of this with statement. */
	Stmt getBody() {
		result = getChildStmt(1)
	}
	
	Stmt getAControlledStmt() {
		result = getBody()
	}
}

/** A switch statement. */
class SwitchStmt extends @switchstmt, ControlStmt {
  /** Get the controlling expression of this switch statement. */
	Expr getExpr() {
		result = getChildExpr(-1)
	}
	
	/** Get the i-th case clause of this switch statement. */
	Case getCase(int i) {
		result = getChildStmt(i)
	}

  /** Get a case clause of this switch statement. */
	Case getACase() {
		result = getCase(_)
	}
	
  /** Get the number of case clauses of this switch statement. */
	int getNumCase() {
	  result = count(getACase())
	}
	
	Case getAControlledStmt() {
		result = getACase()
	}
}

/** A return statement. */
class ReturnStmt extends @returnstmt, JumpStmt {
  /** Get the expression specifying the returned value, if any. */
	Expr getExpr() {
		result = getChildExpr(0)
	}
	
	/** Get the target of this return statement, which is the enclosing statement container. */
	Function getTarget() {
		result = getContainer()
	}

	CFGNode getFirstCFGNode() {
	  if exists(getExpr()) then
	    result = getExpr().getFirstCFGNode()
	  else
	    result = this
	}

  predicate isSubjectToSemicolonInsertion() {
    any()
  }
}

/** A throw statement. */
class ThrowStmt extends @throwstmt, JumpStmt {
  /** Get the expression specifying the value to throw. */
	Expr getExpr() {
		result = getChildExpr(0)
	}
	
	/**
	 * Get the target of this throw statement, which is the closest surrounding
	 * try statement in whose body the throw statement occurs. If
	 * there is no such try statement, the target defaults to the
	 * enclosing statement container.
	 */
	ASTNode getTarget() {
		if exists (TryStmt ts | getParentStmt+() = ts.getBody()) then
			(getParentStmt+() = ((TryStmt)result).getBody() and
			 not exists (TryStmt mid | getParentStmt+() = mid.getBody() and mid.getParentStmt+() = result))
		else
			result = getContainer()
	}

	CFGNode getFirstCFGNode() {
	  result = getExpr().getFirstCFGNode()
	}

  predicate isSubjectToSemicolonInsertion() {
    any()
  }
}

/** A try statement. */
class TryStmt extends @trystmt, ControlStmt {
  /** Get the body of this try statement. */
	BlockStmt getBody() {
		result = getChildStmt(0)
	}
	
	Stmt getAControlledStmt() {
		result = getBody() or
		result = getACatchClause() or
		result = getFinally()
	}
	
	/** Get the i-th catch clause of this try statement, if any. */
	CatchClause getCatchClause(int i) {
	  exists (int idx | 
	    result = getChildStmt(idx) and
	    idx >= 1 and
	    i = idx-1
	  )
	}

	/** Get some catch clause of this try statement. */
	CatchClause getACatchClause() {
	  result = getCatchClause(_)
	}

	/** Get the (unique) unguarded catch clause of this try statement, if any. */
	CatchClause getCatchClause() {
	  result = getACatchClause() and
	  not exists(result.getGuard())
	}

	/** Get the number of catch clauses of this try statement. */
	int getNumCatchClause() {
	  result = count(getACatchClause())
	}
	
	/** Get the finally block of this try statement, if any. */
	BlockStmt getFinally() {
		result = getChildStmt(-1)
	}
}

/** A while loop. */
class WhileStmt extends @whilestmt, LoopStmt {
  /** Get the loop condition of this while loop. */
	Expr getExpr() {
		result = getChildExpr(0)
	}
	
	Expr getTest() {
		result = getExpr()
	}
	
	Stmt getBody() {
		result = getChildStmt(1)
	}
}

/** A do-while loop. */
class DoWhileStmt extends @dowhilestmt, LoopStmt {
  /** Get the loop condition of this do-while loop. */
	Expr getExpr() {
		result = getChildExpr(1)
	}
	
	Expr getTest() {
		result = getExpr()
	}
	
	Stmt getBody() {
		result = getChildStmt(0)
	}

  predicate isSubjectToSemicolonInsertion() {
    any()
  }
}

/** An expression or a variable declaration statement. */
class ExprOrVarDecl extends ASTNode {
	ExprOrVarDecl() {
		this instanceof Expr or
		this instanceof DeclStmt
	}
}

/** A for loop. */
class ForStmt extends @forstmt, LoopStmt {
  /** Get the init part of this for loop. */
	ExprOrVarDecl getInit() {
		result = getChildExpr(0) or
		result = getChildStmt(0)
	}
	
	Expr getTest() {
		result = getChildExpr(1)
	}
	
  /** Get the update part of this for loop. */
	Expr getUpdate() {
		result = getChildExpr(2)
	}
	
	Stmt getBody() {
		result = getChildStmt(3)
	}
}

/** A for-in or for-of loop. */
abstract class EnhancedForLoop extends LoopStmt {
  /**
   * Get the iterator of this for-in or for-of loop; this can be either a
   * pattern, a property reference, or a variable declaration statement.
   */
  ExprOrVarDecl getIterator() {
    result = getChildExpr(0) or
    result = getChildStmt(0)
  }

  /**
   * Get the default value of the loop's iterator, if any.
   */
  Expr getDefault() {
    result = getChildExpr(-1)
  }

  /**
   * Get the iterator expression of this for-in or for-of loop; this can be
   * either a variable access or a variable declarator.
   */
  Expr getIteratorExpr() {
    result = getIterator() or
    result = getIterator().(DeclStmt).getADecl()
  }

  /**
   * Get an iterator variable of this for-in or for-of loop.
   */
  Variable getAnIterationVariable() {
    result = getIterator().(DeclStmt).getADecl().getBindingPattern().getAVariable() or
    result = getIterator().(BindingPattern).getAVariable()
  }

  Expr getTest() {
    none()
  }

  /** Get the expression this for-in or for-of loop iterates over. */
  Expr getIterationDomain() {
    result = getChildExpr(1)
  }

  Stmt getBody() {
    result = getChildStmt(2)
  }
}

/** A for-in loop. */
class ForInStmt extends @forinstmt, EnhancedForLoop {}

/** A for-of loop. */
class ForOfStmt extends @forofstmt, EnhancedForLoop {}

/** A for each-in loop. */
class ForEachStmt extends @foreachstmt, EnhancedForLoop {}

/** A debugger statement. */
class DebuggerStmt extends @debuggerstmt, Stmt {
  predicate isSubjectToSemicolonInsertion() {
    any()
  }
}

/** A function declaration statement. */
class FunctionDeclStmt extends @functiondeclstmt, Stmt, Function {
  Stmt getEnclosingStmt() {
    result = this
  }

  /** Get the JSDoc comment for this function, if any. */
  JSDoc getDocumentation() {
    result = Stmt.super.getDocumentation()
  }

	string toString() {
		result = Stmt.super.toString()
	}
}

/** A declaration statement, i.e., a 'var', 'const' or 'let' declaration. */
class DeclStmt extends @declstmt, Stmt {
	/** Get the i-th declarator in this declaration statement. */
	VariableDeclarator getDecl(int i) {
		result = getChildExpr(i) and i >= 0
	}
	
	/** Get some declarator in this declaration statement. */
	VariableDeclarator getADecl() {
		result = getDecl(_)
	}

  predicate isSubjectToSemicolonInsertion() {
    // exclude variable declarations in the init part of for/for-in/for-of loops
    not exists (LoopStmt for | this = for.getAChildStmt() and this != for.getBody())
  }
}

/** A 'var' declaration statement. */
class VarDeclStmt extends @vardeclstmt, DeclStmt {}

/** A 'const' declaration statement. */
class ConstDeclStmt extends @constdeclstmt, DeclStmt {}

/** A 'let' declaration statement. */
class LetStmt extends @letstmt, DeclStmt {}

/** A legacy let statement of the form `let(vardecls) stmt`. */
class LegacyLetStmt extends @legacy_letstmt, DeclStmt {
  /** Get the statement this let statement scopes over. */
  Stmt getBody() {
    result = getChildStmt(-1)
  }

  predicate isSubjectToSemicolonInsertion() { none() }
}

/** A case or default clause in a switch statement. */
class Case extends @case, Stmt {
  /** Get the test expression of this case clause. */
	Expr getExpr() {
		result = getChildExpr(-1)
	}
	
	/** Is this a default clause? */
	predicate isDefault() {
		not exists(getExpr())
	}
	
	/** Get the i-th statement in this case clause. */
	Stmt getBodyStmt(int i) {
		result = getChildStmt(i)
	}
	
	/** Get some statement in this case clause. */
	Stmt getABodyStmt() {
		result = getChildStmt(_)
	}
	
	/** Get the number of statements in this case clause. */
	int getNumBodyStmt() {
		result = count(getABodyStmt())
	}

	/** Get the switch statement to which this clause belongs. */
	SwitchStmt getSwitch() {
		result = getParent()
	}
}

/** A catch clause. */
class CatchClause extends @catchclause, ControlStmt, Parameterized {
  /** Get the body of this catch clause. */
	BlockStmt getBody() {
		result = getChildStmt(1)
	}
	
	/** Get the guard expression of this catch clause, if any. */
	Expr getGuard() {
	  result = getChildExpr(2)
	}
	
	Stmt getAControlledStmt() {
	  result = getBody()
	}
	
	/** Get the scope induced by this catch clause. */
	CatchScope getScope() {
		result.getCatchClause() = this
	}

	JSDoc getDocumentation() {
		result = ControlStmt.super.getDocumentation()
	}
	
	string toString() {
		result = ControlStmt.super.toString()
	}
}
