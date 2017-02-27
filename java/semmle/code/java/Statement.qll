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
 * A library for working with Java statements.
 */

import Expr
import metrics.MetricStmt
private import Successor

/** A common super-class of all statements. */
class Stmt extends StmtParent, ExprParent, @stmt {
  /** A printable representation of this statement. */
  /*abstract*/ string toString() { result = "stmt" }

  /** A printable representation of this statement. May include more detail than `toString()`. */
  string pp() { result = "stmt" }

  /**
   * The immediately enclosing callable (method or constructor)
   * whose body contains this statement.
   */
  Callable getEnclosingCallable() { stmts(this,_,_,_,result) }

  /** The index of this statement as a child of its parent. */
  int getIndex() { stmts(this,_,_,result,_) }

  /** The parent of this statement. */
  StmtParent getParent() { stmts(this,_,result,_,_) }

  /** Whether this statement is the child of the specified parent at the specified (zero-based) position. */
  predicate isNthChildOf(StmtParent parent, int index) {
    this.getParent() = parent and this.getIndex() = index
  }

  /** The compilation unit in which this statement occurs. */
  CompilationUnit getCompilationUnit() { result = this.getFile() }

  /** A child of this statement, if any. */
  Stmt getAChild() { result.getParent() = this }

  /**
   * An immediate successor of this statement.
   *
   * DEPRECATED: use `ControlFlowNode.getASuccessor()` instead.
   */
  deprecated StmtParent getASuccessor() { result = stmtSucc(this) }

  /**
   * An immediate predecessor of this statement.
   *
   * DEPRECATED: use `ControlFlowNode.getAPredecessor()` instead.
   */
  deprecated Stmt getAPredecessor() { this = stmtSucc(result) }

  /** The basic block in which this statement occurs. */
  BasicBlock getBasicBlock() { result.getANode() = this }
  
  /** Cast this statement to a class that provides access to metrics information. */
  MetricStmt getMetrics() { result = this }

  /** This statement's Halstead ID (used to compute Halstead metrics). */
  string getHalsteadID() { result = "Stmt" }
}

/** A statement parent is any element that can have a statement as its child. */
class StmtParent extends @stmtparent, Top {
}

/** A block of statements. */
class Block extends Stmt,@block {
  /** A statement that is an immediate child of this block. */
  Stmt getAStmt() { result.getParent() = this }

  /** The immediate child statement of this block that occurs at the specified (zero-based) position. */
  Stmt getStmt(int index) { result.getIndex() = index and result.getParent() = this }

  /** The number of immediate child statements in this block. */
  int getNumStmt() { result = count(this.getAStmt()) }

  /** The last statement in this block. */
  Stmt getLastStmt() { result = getStmt(getNumStmt()-1) }

  /** A printable representation of this statement. May include more detail than `toString()`. */
  string pp() { result = "{ ... }" }

  /** This statement's Halstead ID (used to compute Halstead metrics). */
  string getHalsteadID() { result = "Block" }
}

/** A block with only a single statement. */
class SingletonBlock extends Block {
  SingletonBlock() { this.getNumStmt() = 1 }

  /** The single statement in this block. */
  Stmt getStmt() { result = getStmt(0) }
}

/**
 * A conditional statement, including `if`, `for`,
 * `while` and `dowhile` statements.
 */
abstract class ConditionalStmt extends Stmt {
  /** The boolean condition of this conditional statement. */
  abstract Expr getCondition();

  /**
   * The statement that is executed whenever the condition
   * of this branch statement evaluates to `true`.
   *
   * DEPRECATED: use `ConditionNode.getATrueSuccessor()` instead.
   */
  deprecated abstract Stmt getTrueSuccessor();
  
  /**
   * The statement that is executed whenever the condition
   * of this branch statement evaluates to `false`.
   *
   * DEPRECATED: use `ConditionNode.getAFalseSuccessor()` instead.
   */
  deprecated cached
  Stmt getFalseSuccessor() { result = getASuccessor() and not result = getTrueSuccessor() }

  /**
   * Any statement that may be executed immediately following
   * evaluation of the condition of this branch statement.
   *
   * DEPRECATED: use `ConditionNode.getABranchSuccessor(_)` instead.
   */
  deprecated Stmt getABranch() {
    result = getTrueSuccessor() or result = getFalseSuccessor()
  }

  /**
   * Given one branch of this conditional statement, return the other one.
   *
   * DEPRECATED: use `ConditionNode.getABranchSuccessor(boolean)` instead.
   */
  deprecated Stmt getOtherBranch(Stmt succ) {
    succ = getTrueSuccessor() and result = getFalseSuccessor() or
    succ = getFalseSuccessor() and result = getTrueSuccessor()
  }
}

/** An `if` statement. */
class IfStmt extends ConditionalStmt,@ifstmt {
  /** The boolean condition of this `if` statement. */
  Expr getCondition() { result.isNthChildOf(this, 0) }

  /** The `then` branch of this `if` statement. */
  Stmt getThen() { result.isNthChildOf(this, 1) }

  /**
   * The statement that is executed whenever the condition
   * of this branch statement evaluates to `true`.
   */
  Stmt getTrueSuccessor() { result = getThen() }

  /** The `else` branch of this `if` statement. */
  Stmt getElse() { result.isNthChildOf(this, 2) }

  /** A printable representation of this statement. May include more detail than `toString()`. */
  string pp() { 
    result = "if (...) " + this.getThen().pp() + " else " + this.getElse().pp()
    or
    (not exists(this.getElse()) and result = "if (...) " + this.getThen().pp())
  }

  /** This statement's Halstead ID (used to compute Halstead metrics). */
  string getHalsteadID() { result = "IfStmt" }
}

/** A `for` loop. */
class ForStmt extends ConditionalStmt,@forstmt {
  /**
   * An initializer expression of the loop.
   *
   * This may be an assignment expression or a
   * local variable declaration expression.
   */
  Expr getAnInit() {
    exists(int index | result.isNthChildOf(this, index) | index <= -1)
  }

  /** The initializer expression of the loop at the specified (zero-based) position. */
  Expr getInit(int index) {
    result = getAnInit() and
    index = -1 - result.getIndex()
  }

  /** The boolean condition of this `for` loop. */
  Expr getCondition() { result.isNthChildOf(this, 1) }

  /** An update expression of this `for` loop. */
  Expr getAnUpdate() {
    exists(int index | result.isNthChildOf(this, index) | index >= 3)
  }

  /** The update expression of this loop at the specified (zero-based) position. */
  Expr getUpdate(int index) {
    result = getAnUpdate() and
    index = result.getIndex() - 3
  }

  /** The body of this `for` loop. */
  Stmt getStmt() { result.getParent() = this and result.getIndex() = 2 }
  
  /**
   * The statement that is executed whenever the condition
   * of this branch statement evaluates to true.
   */
  Stmt getTrueSuccessor() { result = getStmt() }

  /**
   * A variable that is used as an iteration variable: it is defined,
   * updated or tested in the head of the `for` statement.
   *
   * This only returns variables that are quite certainly loop variables;
   * for complex iterations, it may not return anything.
   *
   * More precisely, it returns variables that are both accessed in the
   * condition of this `for` statement and updated in the update expression
   * of this for statement but may be initialized elsewhere.
   */
  Variable getAnIterationVariable() {
    // Check that the variable is assigned to, incremented or decremented in the update expression, and...
    exists(Expr update | update = getAnUpdate().getAChildExpr*() |
      update.(UnaryAssignExpr).getExpr() = result.getAnAccess() or
      update = result.getAnAssignedValue()
    ) and
    // ...that it is checked or used in the condition.
    getCondition().getAChildExpr*() = result.getAnAccess()
  }

  /** A printable representation of this statement. May include more detail than `toString()`. */
  string pp() {
    result = "for (...;...;...) " + this.getStmt().pp()
  }

  /** This statement's Halstead ID (used to compute Halstead metrics). */
  string getHalsteadID() { result = "ForStmt" }
}

/** An enhanced `for` loop. (Introduced in Java 5.) */
class EnhancedForStmt extends Stmt,@enhancedforstmt {
  /** The local variable declaration expression of this enhanced `for` loop. */
  LocalVariableDeclExpr getVariable() { result.getParent() = this }

  /** The expression over which this enhanced `for` loop iterates. */
  Expr getExpr() { result.isNthChildOf(this, 1) }

  /** The body of this enhanced `for` loop. */
  Stmt getStmt() { result.getParent() = this }

  /** A printable representation of this statement. May include more detail than `toString()`. */
  string pp() {
    result = "for (...) " + this.getStmt().pp()
  }

  /** This statement's Halstead ID (used to compute Halstead metrics). */
  string getHalsteadID() { result = "EnhancedForStmt" }
}

/** A `while` loop. */
class WhileStmt extends ConditionalStmt,@whilestmt {
  /** The boolean condition of this `while` loop. */
  Expr getCondition() { result.getParent() = this }

  /** The body of this `while` loop. */
  Stmt getStmt() { result.getParent() = this }

  /**
   * The statement that is executed whenever the condition
   * of this branch statement evaluates to true.
   */
  Stmt getTrueSuccessor() { result = getStmt() }

  /** A printable representation of this statement. May include more detail than `toString()`. */
  string pp() {
    result = "while (...) " + this.getStmt().pp()
  }

  /** This statement's Halstead ID (used to compute Halstead metrics). */
  string getHalsteadID() { result = "WhileStmt" }
}

/** A `do` loop. */
class DoStmt extends ConditionalStmt,@dostmt {
  /** The condition of this `do` loop. */
  Expr getCondition() { result.getParent() = this }

  /** The body of this `do` loop. */
  Stmt getStmt() { result.getParent() = this }

  /**
   * The statement that is executed whenever the condition
   * of this branch statement evaluates to `true`.
   */
  Stmt getTrueSuccessor() { result = getStmt() }

  /** A printable representation of this statement. May include more detail than `toString()`. */
  string pp() {
    result = "do " + this.getStmt().pp() + " while (...)" 
  }

  /** This statement's Halstead ID (used to compute Halstead metrics). */
  string getHalsteadID() { result = "DoStmt" }
}

/**
 * A loop statement, including `for`, enhanced `for`,
 * `while` and `do` statements.
 */
class LoopStmt extends Stmt {
   LoopStmt() {
        this instanceof ForStmt
     or this instanceof EnhancedForStmt
     or this instanceof WhileStmt 
     or this instanceof DoStmt
   }

  /** The body of this loop statement. */
  Stmt getBody() {
    result = this.(ForStmt).getStmt() or
    result = this.(EnhancedForStmt).getStmt() or
    result = this.(WhileStmt).getStmt() or
    result = this.(DoStmt).getStmt()
  }

  /** The boolean condition of this loop statement. */
  Expr getCondition() {
    result = this.(ForStmt).getCondition() or
    result = this.(WhileStmt).getCondition() or
    result = this.(DoStmt).getCondition()
  }
}

/** A `try` statement. */
class TryStmt extends Stmt,@trystmt {
  /** The block of the `try` statement. */
  Stmt getBlock() { result.isNthChildOf(this, -1) }

  /** A `catch` clause of this `try` statement. */
  CatchClause getACatchClause() { result.getParent() = this }

  /**
   * The `catch` clause at the specified (zero-based) position
   * in this `try` statement.
   */
  CatchClause getCatchClause(int index) {
    result = this.getACatchClause() and
    result.getIndex() = index
  }

  /** The `finally` block, if any. */
  Block getFinally() { result.isNthChildOf(this, -2) }
  
  /** A resource variable declaration, if any. */
  LocalVariableDeclStmt getAResourceDecl() {
    result.getParent() = this and result.getIndex() <= -3
  }
  
  /** The resource variable declaration at the specified position in this `try` statement. */
  LocalVariableDeclStmt getResourceDecl(int index) {
    result = this.getAResourceDecl() and
    index = -3 - result.getIndex()
  }

  /** A printable representation of this statement. May include more detail than `toString()`. */
  string pp() {
    result = "try " + this.getBlock().pp() + " catch (...)"
  }

  /** This statement's Halstead ID (used to compute Halstead metrics). */
  string getHalsteadID() { result = "TryStmt" }
}

/** A `catch` clause in a `try` statement. */
class CatchClause extends Stmt,@catchclause {
  /** The block of this `catch` clause. */
  Block getBlock() { result.getParent() = this }

  /** The `try` statement in which this `catch` clause occurs. */
  TryStmt getTry() { this = result.getACatchClause() }

  /** The parameter of this `catch` clause. */
  LocalVariableDeclExpr getVariable() { result.getParent() = this }
  
  /** Whether this `catch` clause is a _multi_-`catch` clause. */
  predicate isMultiCatch() {
    this.getVariable().getTypeAccess() instanceof UnionTypeAccess
  }

  /** A type caught by this `catch` clause. */
  RefType getACaughtType() {
    exists (Expr ta | ta = getVariable().getTypeAccess() |
      result = ta.(TypeAccess).getType() or
      result = ta.(UnionTypeAccess).getAnAlternative().getType()
    )
  }

  /** A printable representation of this statement. May include more detail than `toString()`. */
  string pp() {
    result = "catch (...) " + this.getBlock().pp()
  }

  /** This statement's Halstead ID (used to compute Halstead metrics). */
  string getHalsteadID() { result = "CatchClause" }
}

/** A `switch` statement. */
class SwitchStmt extends Stmt,@switchstmt {
  /** An immediate child statement of this `switch` statement. */
  Stmt getAStmt() { result.getParent() = this }

  /**
   * The immediate child statement of this `switch` statement
   * that occurs at the specified (zero-based) position.
   */
  Stmt getStmt(int index) { result = this.getAStmt() and result.getIndex() = index }

  /**
   * A case of this `switch` statement,
   * which may be either a normal `case` or a `default`.
   */
  Stmt getACase() { result = getAConstCase() or result = getDefaultCase() }

  /** A (non-default) `case` of this `switch` statement. */
  ConstCase getAConstCase() { result.getParent() = this }

  /** The `default` case of this switch statement, if any. */
  DefaultCase getDefaultCase() { result.getParent() = this }

  /** The expression of this `switch` statement. */
  Expr getExpr() { result.getParent() = this }

  /** A printable representation of this statement. May include more detail than `toString()`. */
  string pp() {
    result = "switch (...)"
  }

  /** This statement's Halstead ID (used to compute Halstead metrics). */
  string getHalsteadID() { result = "SwitchStmt" }
}

/**
 * A case of a `switch` statement.
 *
 * This includes both normal `case`s and the `default` case.
 */
abstract class SwitchCase extends Stmt {
}

/** A constant `case` of a switch statement. */
class ConstCase extends SwitchCase, @case {
  ConstCase() { exists(Expr e | e.getParent() = this) }

  /** The expression of this `case`. */
  Expr getValue() { result.getParent() = this }

  /** A printable representation of this statement. May include more detail than `toString()`. */
  string pp() {
    result = "case ...:"
  }

  /** This statement's Halstead ID (used to compute Halstead metrics). */
  string getHalsteadID() { result = "ConstCase" }
}

/** A `default` case of a `switch` statement */
class DefaultCase extends SwitchCase, @case {
  DefaultCase() { not exists(Expr e | e.getParent() = this) }

  /** A printable representation of this statement. May include more detail than `toString()`. */
  string pp() {
    result = "default"
  }

  /** This statement's Halstead ID (used to compute Halstead metrics). */
  string getHalsteadID() { result = "DefaultCase" }
}

/** A `synchronized` statement. */
class SynchronizedStmt extends Stmt,@synchronizedstmt {
  /** The expression on which this `synchronized` statement synchronizes. */
  Expr getExpr() { result.getParent() = this }

  /** The block of this `synchronized` statement. */
  Stmt getBlock() { result.getParent() = this }

  /** A printable representation of this statement. May include more detail than `toString()`. */
  string pp() {
    result = "synchronized (...) " + this.getBlock().pp()
  }

  /** This statement's Halstead ID (used to compute Halstead metrics). */
  string getHalsteadID() { result = "SynchronizedStmt" }
}

/** A `return` statement. */
class ReturnStmt extends Stmt,@returnstmt {
  /** The expression returned by this `return` statement, if any. */
  Expr getResult() { result.getParent() = this }

  /** A printable representation of this statement. May include more detail than `toString()`. */
  string pp() {
    result = "return ..."
  }

  /** This statement's Halstead ID (used to compute Halstead metrics). */
  string getHalsteadID() { result = "ReturnStmt" }
}

/** A `throw` statement. */
class ThrowStmt extends Stmt,@throwstmt {
  /** The expression thrown by this `throw` statement. */
  Expr getExpr() { result.getParent() = this }

  /** A printable representation of this statement. May include more detail than `toString()`. */
  string pp() {
    result = "throw ..."
  }

  /** This statement's Halstead ID (used to compute Halstead metrics). */
  string getHalsteadID() { result = "ThrowStmt" }

  /** The type of the expression thrown by this `throw` statement. */
  RefType getThrownExceptionType() { result = getExpr().getType() }

  /**
   * The `catch` clause that catches the exception
   * thrown by this `throws` statement and occurs
   * in the same method as this `throws` statement,
   * provided such a `catch` exists.
   */
  CatchClause getLexicalCatchIfAny() {
    exists(TryStmt try | try = findEnclosing() and result = catchClauseForThis(try))
  }
  
  private Stmt findEnclosing() {
    result = getParent() or 
    exists(Stmt mid | 
      mid = findEnclosing() and
      not exists(this.catchClauseForThis((TryStmt)mid)) and
      result = mid.getParent()
    )
  }

  private CatchClause catchClauseForThis(TryStmt try) {
    result = try.getACatchClause() and
    result.getEnclosingCallable() = this.getEnclosingCallable() and
    ((RefType)getExpr().getType()).hasSupertype*((RefType)result.getVariable().getType()) and
    not this.getParent+() = result
  }
}

/** A `break` or `continue` statement. */
class JumpStmt extends Stmt {
  JumpStmt() {
    this instanceof BreakStmt or
    this instanceof ContinueStmt
  }
  
  /**
   * The labeled statement that this `break` or
   * `continue` statement refers to, if any.
   */
  LabeledStmt getTargetLabel() {
    this.getParent+() = result and
    namestrings(result.getLabel(), _, this)
  }
  
  private Stmt getLabelTarget() {
    result = getTargetLabel().getStmt()
  }
  
  private Stmt getAPotentialTarget() {
    this.getParent+() = result and
    (result instanceof LoopStmt or
     this instanceof BreakStmt and result instanceof SwitchStmt)
  }

  private Stmt getEnclosingTarget() {
    result = getAPotentialTarget() and
    not exists (Stmt other | other = getAPotentialTarget() | other.getParent+() = result)
  }
  
  /**
   * The statement that this `break` or `continue` jumps to.
   */
  Stmt getTarget() {
    result = getLabelTarget() or
    (not exists(getLabelTarget()) and result = getEnclosingTarget())
  }
}

/** A `break` statement. */
class BreakStmt extends Stmt,@breakstmt {
  /** The label targeted by this `break` statement, if any. */
  string getLabel() { namestrings(result,_,this) }

  /** Whether this `break` statement has an explicit label. */
  predicate hasLabel() { exists(string s | s = this.getLabel()) }

  /** A printable representation of this statement. May include more detail than `toString()`. */
  string pp() {
    if this.hasLabel() then
      result = "break " + this.getLabel()
    else
      result = "break"
  }

  /** This statement's Halstead ID (used to compute Halstead metrics). */
  string getHalsteadID() { result = "BreakStmt" }
}

/** A `continue` statement. */
class ContinueStmt extends Stmt,@continuestmt {
  /** The label targeted by this `continue` statement, if any. */
  string getLabel() { namestrings(result,_,this) }

  /** Whether this `continue` statement has an explicit label. */
  predicate hasLabel() { exists(string s | s = this.getLabel()) }

  /** A printable representation of this statement. May include more detail than `toString()`. */
  string pp() {
    if this.hasLabel() then
      result = "continue " + this.getLabel()
    else
      result = "continue"
  }

  /** This statement's Halstead ID (used to compute Halstead metrics). */
  string getHalsteadID() { result = "ContinueStmt" }
}

/** The empty statement. */
class EmptyStmt extends Stmt,@emptystmt {
  /** A printable representation of this statement. May include more detail than `toString()`. */
  string pp() {
    result = ";"
  }

  /** This statement's Halstead ID (used to compute Halstead metrics). */
  string getHalsteadID() { result = "EmptyStmt" }
}

/**
 * An expression statement.
 *
 * Certain kinds of expressions may be used as statements by appending a semicolon.
 */
class ExprStmt extends Stmt,@exprstmt {
  /** The expression of this expression statement. */
  Expr getExpr() { result.getParent() = this }

  /** A printable representation of this statement. May include more detail than `toString()`. */
  string pp() {
    result = "...;"
  }

  /** This statement's Halstead ID (used to compute Halstead metrics). */
  string getHalsteadID() { result = "ExprStmt" }

  /** Whether this statement represents a field declaration with an initializer. */
  predicate isFieldDecl() {
    getEnclosingCallable() instanceof InitializerMethod and
    exists (FieldDeclaration fd, Location fdl, Location sl |
      fdl = fd.getLocation() and sl = getLocation() |
      fdl.getFile() = sl.getFile() and
      fdl.getStartLine() = sl.getStartLine() and
      fdl.getStartColumn() = sl.getStartColumn()
    )
  }
}

/** A labeled statement. */
class LabeledStmt extends Stmt,@labeledstmt {
  /** The statement of this labeled statement. */
  Stmt getStmt() { result.getParent() = this }

  /** The label of this labeled statement. */
  string getLabel() { namestrings(result,_,this) }

  /** A printable representation of this statement. May include more detail than `toString()`. */
  string pp() {
    result = this.getLabel() + ": " + this.getStmt().pp()
  }

  /** This statement's Halstead ID (used to compute Halstead metrics). */
  string getHalsteadID() { result = this.getLabel() + ":" }
}

/** An `assert` statement. */
class AssertStmt extends Stmt,@assertstmt {
  /** The boolean expression of this `assert` statement. */
  Expr getExpr() { exprs(result,_,_,this,_) and result.getIndex() = 0 }

  /** The assertion message expression, if any. */
  Expr getMessage() { exprs(result,_,_,this,_) and result.getIndex() = 1 }

  /** A printable representation of this statement. May include more detail than `toString()`. */
  string pp() {
    if exists(this.getMessage()) then
      result = "assert ... : ..."
    else
      result = "assert ..."
  }

  /** This statement's Halstead ID (used to compute Halstead metrics). */
  string getHalsteadID() { result = "AssertStmt" }
}

/** A statement that declares one or more local variables. */
class LocalVariableDeclStmt extends Stmt,@localvariabledeclstmt {
  /** A declared variable. */
  LocalVariableDeclExpr getAVariable() { result.getParent() = this }

  /** The variable declared at the specified (one-based) position in this local variable declaration statement. */
  LocalVariableDeclExpr getVariable(int index) {
    result = this.getAVariable() and
    result.getIndex() = index
  }

  /** An index of a variable declared in this local variable declaration statement. */
  int getAVariableIndex() { 
    exists(getVariable(result))
  }

  /** A printable representation of this statement. May include more detail than `toString()`. */
  string pp() {
    result = "local variable declaration"
  }

  /** This statement's Halstead ID (used to compute Halstead metrics). */
  string getHalsteadID() { result = "LocalVariableDeclStmt" }
}

/** A statement that declares a local class. */
class LocalClassDeclStmt extends Stmt,@localclassdeclstmt {
  /** The local class declared by this statement. */
  LocalClass getLocalClass() { isLocalClass(result,this) }

  /** A printable representation of this statement. May include more detail than `toString()`. */
  string pp() {
    result = "local class declaration: " + this.getLocalClass().toString()
  }

  /** This statement's Halstead ID (used to compute Halstead metrics). */
  string getHalsteadID() { result = "LocalClassDeclStmt" }
}

/** An explicit `this(...)` constructor invocation. */
class ThisConstructorInvocationStmt extends Stmt, ConstructorCall, @constructorinvocationstmt {
  /** An argument of this constructor invocation. */
  override Expr getAnArgument() { result.getIndex() >= 0 and result.getParent() = this }

  /** The argument at the specified (zero-based) position in this constructor invocation. */
  override Expr getArgument(int index) {
    result = this.getAnArgument() and
    result.getIndex() = index
  }

  /** A type argument of this constructor invocation. */
  Expr getATypeArgument() { result.getIndex() <= -2 and result.getParent() = this }

  /** The type argument at the specified (zero-based) position in this constructor invocation. */
  Expr getTypeArgument(int index) {
    result = this.getATypeArgument() and
    (-2 - result.getIndex()) = index
  }

  /** The constructor invoked by this constructor invocation. */
  Constructor getConstructor() { callableBinding(this,result) }

  override Expr getQualifier() { none() }

  /** The immediately enclosing callable of this constructor invocation. */
  override Callable getEnclosingCallable() { result = Stmt.super.getEnclosingCallable() }

  /** The immediately enclosing statement of this constructor invocation. */
  override Stmt getEnclosingStmt() { result = this }

  /** A printable representation of this statement. May include more detail than `toString()`. */
  string pp() {
    result = "this(...)"
  }

  /** A printable representation of this statement. */
  string toString() { result = pp() }

  /** This statement's Halstead ID (used to compute Halstead metrics). */
  string getHalsteadID() { result = "ConstructorInvocationStmt" }
}

/** An explicit `super(...)` constructor invocation. */
class SuperConstructorInvocationStmt extends Stmt, ConstructorCall, @superconstructorinvocationstmt {
  /** An argument of this constructor invocation. */
  override Expr getAnArgument() { result.getIndex() >= 0 and result.getParent() = this }

  /** The argument at the specified (zero-based) position in this constructor invocation. */
  override Expr getArgument(int index) {
    result = this.getAnArgument() and
    result.getIndex() = index
  }

  /** A type argument of this constructor invocation. */
  Expr getATypeArgument() { result.getIndex() <= -2 and result.getParent() = this }

  /** The type argument at the specified (zero-based) position in this constructor invocation. */
  Expr getTypeArgument(int index) {
    result = this.getATypeArgument() and
    (-2 - result.getIndex()) = index
  }

  /** The constructor invoked by this constructor invocation. */
  Constructor getConstructor() { callableBinding(this,result) }

  /** The qualifier expression of this `super(...)` constructor invocation, if any. */
  override Expr getQualifier() { result.isNthChildOf(this, -1) }

  /** The immediately enclosing callable of this constructor invocation. */
  override Callable getEnclosingCallable() { result = Stmt.super.getEnclosingCallable() }

  /** The immediately enclosing statement of this constructor invocation. */
  override Stmt getEnclosingStmt() { result = this }

  /** A printable representation of this statement. May include more detail than `toString()`. */
  string pp() {
    result = "super(...)"
  }

  /** A printable representation of this statement. */
  string toString() { result = pp() }

  /** This statement's Halstead ID (used to compute Halstead metrics). */
  string getHalsteadID() { result = "SuperConstructorInvocationStmt" }
}
