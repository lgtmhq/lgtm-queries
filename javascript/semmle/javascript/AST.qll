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
 * Provides classes for working with the AST-based representation of JavaScript programs.
 */

import Locations
import Expr
import Stmt
import CFG

/**
 * A program element corresponding to JavaScript code, such as an expression
 * or a statement.
 *
 * This class provides generic traversal methods applicable to all AST nodes,
 * such as obtaining the children of an AST node.
 */
class ASTNode extends @ast_node, Locatable {
  /** Gets the toplevel syntactic unit to which this element belongs. */
  cached
  TopLevel getTopLevel() {
    result = getParent().getTopLevel()
  }

  /**
   * Gets the `i`th child node of this node.
   *
   * _Note_: The indices of child nodes are considered an implementation detail and may
   * change between versions of the extractor.
   */
  ASTNode getChild(int i) {
    result = getChildExpr(i) or
    result = getChildStmt(i) or
    properties(result, this, i, _, _) or
    classes(result, this, _) and i = 2
  }

  /** Gets the `i`th child statement of this node. */
  Stmt getChildStmt(int i) {
    stmts(result, _, this, i, _)
  }

  /** Gets the `i`th child expression of this node. */
  Expr getChildExpr(int i) {
    exprs(result, _, this, i, _)
  }

  /** Gets a child node of this node. */
  ASTNode getAChild() {
    result = getChild(_)
  }

  /** Gets a child expression of this node. */
  Expr getAChildExpr() {
    result = getChildExpr(_)
  }

  /** Gets a child statement of this node. */
  Stmt getAChildStmt() {
    result = getChildStmt(_)
  }

  /** Gets the number of child nodes of this node. */
  int getNumChild() {
    result = count(getAChild())
  }

  /** Gets the number of child expressions of this node. */
  int getNumChildExpr() {
    result = count(getAChildExpr())
  }

  /** Gets the number of child statements of this node. */
  int getNumChildStmt() {
    result = count(getAChildStmt())
  }

  /** Gets the parent node of this node, if any. */
  ASTNode getParent() {
    this = result.getAChild()
  }

  /** Gets the first control flow node belonging to this syntactic entity. */
  ControlFlowNode getFirstControlFlowNode() {
    result = this
  }

  /**
   * DEPRECATED: Use `getFirstControlFlowNode` instead.
   *
   * Gets the first control flow node belonging to this syntactic entity.
   */
  deprecated
  ControlFlowNode getFirstCFGNode() {
    result = getFirstControlFlowNode()
  }

  /** Holds if this syntactic entity belongs to an externs file. */
  predicate inExternsFile() {
    getTopLevel().isExterns()
  }
}

/**
 * A toplevel syntactic unit; that is, a stand-alone script, an inline script
 * embedded in an HTML `<script>` tag, a code snippet assigned to an HTML event
 * handler attribute, or a `javascript:` URL.
 */
class TopLevel extends @toplevel, StmtContainer {
  /** Holds if this toplevel is minified. */
  predicate isMinified() {
    // file name contains 'min' (not as part of a longer word)
    getFile().getName().regexpMatch(".*[^-.]*[-.]min([-.].*)?\\.\\w+")
    or
    exists (int numstmt | numstmt = strictcount(Stmt s | s.getTopLevel() = this) |
      // there are more than two statements per line on average
      (float)numstmt / getNumberOfLines() > 2 and
      // and there are at least ten statements overall
      numstmt >= 10
    )
  }

  /** Holds if this toplevel is an externs definitions file. */
  predicate isExterns() {
    // either it was explicitly extracted as an externs file...
    isExterns(this) or
    // ...or it has a comment with an `@externs` tag in it
    exists (JSDocTag externs |
      externs.getTitle() = "externs" and
      externs.getTopLevel() = this
    )
  }

  /** Gets the toplevel to which this element belongs, that is, itself. */
  override TopLevel getTopLevel() {
    result = this
  }

  /** Gets the number of lines in this toplevel. */
  int getNumberOfLines() {
    numlines(this, result, _, _)
  }

  /** Gets the number of lines containing code in this toplevel. */
  int getNumberOfLinesOfCode() {
    numlines(this, _, result, _)
  }

  /** Gets the number of lines containing comments in this toplevel. */
  int getNumberOfLinesOfComments() {
    numlines(this, _, _, result)
  }

  override predicate isStrict() {
    getAStmt() instanceof StrictModeDecl
  }

  override ControlFlowNode getFirstControlFlowNode() {
    result = getEntry()
  }

  override string toString() {
    result = "<toplevel>"
  }
}

/**
 * A script originating from an HTML `<script>` element.
 */
abstract class Script extends TopLevel {
}

/**
 * An external script originating from an HTML `<script>` element.
 */
class ExternalScript extends @script, Script {
}

/**
 * A script embedded inline in an HTML `<script>` element.
 */
class InlineScript extends @inline_script, Script {
}

/**
 * A code snippet originating from an HTML attribute value.
 */
abstract class CodeInAttribute extends TopLevel {
}

/**
 * A code snippet originating from an event handler attribute.
 */
class EventHandlerCode extends @event_handler, CodeInAttribute {
}

/**
 * A code snippet originating from a URL with the `javascript:` URL scheme.
 */
class JavaScriptURL extends @javascript_url, CodeInAttribute {
}

/**
 * A toplevel syntactic entity containing Closure-style externs definitions.
 */
class Externs extends TopLevel {
  Externs() {
    isExterns()
  }
}

/** A program element that is either an expression or a statement. */
class ExprOrStmt extends @exprorstmt, ControlFlowNode, ASTNode {}

/**
 * A program element that contains statements, but isn't itself
 * a statement, in other words a toplevel or a function.
 */
class StmtContainer extends @stmt_container, ASTNode {
  /** Gets the innermost enclosing container in which this container is nested. */
  StmtContainer getEnclosingContainer() {
    none()
  }

  /** Gets a statement that belongs to this container. */
  Stmt getAStmt() {
    result.getContainer() = this
  }

  /**
   * Gets the body of this container.
   *
   * For scripts or modules, this is the container itself; for functions,
   * it is the function body.
   */
  ASTNode getBody() {
    result = this
  }

  /**
   * Gets the (unique) entry node of the control flow graph for this toplevel or function.
   *
   * For most purposes, the start node should be used instead of the entry node;
   * see predicate `getStart()`.
   */
  ControlFlowEntryNode getEntry() {
    result.getContainer() = this
  }

  /** Gets the (unique) exit node of the control flow graph for this toplevel or function. */
  ControlFlowExitNode getExit() {
    result.getContainer() = this
  }

  /**
   * Gets the (unique) CFG node at which execution of this toplevel or function begins.
   *
   * Unlike the entry node, which is a synthetic construct, the start node corresponds to
   * an actual program element, such as the first statement of a toplevel or the first
   * parameter of a function.
   *
   * Empty toplevels do not have a start node.
   */
  ConcreteControlFlowNode getStart() {
    successor(getEntry(), result)
  }

  /**
   * Gets the entry basic block of this function, that is, the basic block
   * containing the entry node of its CFG.
   */
  EntryBasicBlock getEntryBB() {
    result = getEntry()
  }

  /**
   * Gets the start basic block of this function, that is, the basic block
   * containing the start node of its CFG.
   */
  BasicBlock getStartBB() {
    result.getANode() = getStart()
  }

  /** Gets the scope induced by this toplevel or function, if any. */
  Scope getScope() {
    scopenodes(this, result)
  }

  /**
   * Holds if the code in this container is executed in ECMAScript strict mode.
   *
   * See Annex C of the ECMAScript language specification.
   */
  predicate isStrict() {
    getEnclosingContainer().isStrict()
  }
}
