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
import Expr
import Stmt
import CFG

/**
 * A syntactic entity corresponding to JavaScript code.
 *
 * This class provides generic traversal methods applicable to all AST nodes,
 * such as obtaining the children of an AST node.
 */
class ASTNode extends @ast_node, Locatable {
  /** Get the toplevel syntactic unit to which this element belongs. */
  cached
  TopLevel getTopLevel() {
    result = getParent().getTopLevel()
  }

  /**
   * Get the i-th child node of this node; the result may be an expression, a statement,
   * a property or a class.
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

  /** Get the i-th child statement of this node. */
  Stmt getChildStmt(int i) {
    stmts(result, _, this, i, _)
  }

  /** Get the i-th child expression of this node. */
  Expr getChildExpr(int i) {
    exprs(result, _, this, i, _)
  }

  /** Get any child node of this node. */
  ASTNode getAChild() {
    result = getChild(_)
  }

  /** Get any child expression of this node. */
  Expr getAChildExpr() {
    result = getChildExpr(_)
  }

  /** Get any child statement of this node. */
  Stmt getAChildStmt() {
    result = getChildStmt(_)
  }

  /** Get the number of child nodes of this node. */
  int getNumChild() {
    result = count(getAChild())
  }

  /** Get the number of child expressions of this node. */
  int getNumChildExpr() {
    result = count(getAChildExpr())
  }

  /** Get the number of child statements of this node. */
  int getNumChildStmt() {
    result = count(getAChildStmt())
  }

  /** Get the parent node of this node, if any. */
  ASTNode getParent() {
    this = result.getAChild()
  }

  /** Get the first control flow node belonging to this syntactic entity. */
  CFGNode getFirstCFGNode() {
    result = this
  }

  /** Does this syntactic entity belong to an externs file? */
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
  /** Is this syntactic unit minified? */
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

  /** Is this syntactic unit an externs definitions file? */
  predicate isExterns() {
    // either it was explicitly extracted as an externs file...
    isExterns(this) or
    // ...or it has a comment with an `@externs` tag in it
    exists (JSDoc jsdoc | jsdoc.getFile().getATopLevel() = this |
      jsdoc.getATag().getTitle() = "externs"
    )
  }
  
  /** Get the toplevel syntactic unit to which this element belongs, that is, itself. */
  TopLevel getTopLevel() {
    result = this
  }

  /** Get the number of lines in this toplevel. */
  int getNumberOfLines() {
    numlines(this, result, _, _)
  }

  /** Get the number of lines containing code in this toplevel. */
  int getNumberOfLinesOfCode() {
    numlines(this, _, result, _)
  }

  /** Get the number of lines containing comments in this toplevel. */
  int getNumberOfLinesOfComments() {
    numlines(this, _, _, result)
  }

  predicate isStrict() {
    getAStmt() instanceof StrictModeDecl
  }

  string toString() {
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
 * Code embedded inline in an HTML `<script>` element.
 */
class InlineScript extends @inline_script, Script {
}

/**
 * Code originating from an HTML attribute value.
 */
abstract class CodeInAttribute extends TopLevel {
}

/**
 * Code originating from an event handler attribute.
 */
class EventHandlerCode extends @event_handler, CodeInAttribute {
}

/**
 * Code originating from a URL with the `javascript:` URL scheme.
 */
class JavaScriptURL extends @javascript_url, CodeInAttribute {
}

/**
 * A toplevel syntactic entity containing Closure-style extern definitions.
 */
class Externs extends TopLevel {
  Externs() {
    isExterns()
  }
}

/** A syntactic entity that is either an expression or a statement. */
class ExprOrStmt extends @exprorstmt, CFGNode, ASTNode {}

/**
 * A syntactic entity that contains statements, but isn't itself
 * a statement: a toplevel syntactic unit or a function.
 */
class StmtContainer extends @stmt_container, ASTNode {
  /** Get the innermost enclosing container in which this container is nested. */
  StmtContainer getEnclosingContainer() {
    none()
  }

  /** Get a statement that in this container. */
  Stmt getAStmt() {
    result.getContainer() = this
  }

  /** Get the (unique) entry node of the control flow graph for this toplevel or function. */
  EntryCFGNode getEntry() {
    result.getContainer() = this
  }

  /** Get the (unique) exit node of the control flow graph for this toplevel or function. */
  ExitCFGNode getExit() {
    result.getContainer() = this
  }

  /**
   * Whether the code in this syntactic entity is executed in ECMAScript strict mode.
   *
   * See Annex C of the ECMAScript 5 and ECMAScript 2015 ("ECMAScript 6") language specifications.
   */
  predicate isStrict() {
    getEnclosingContainer().isStrict()
  }
}
