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
 * Classes for working with xUnit.js tests.
 */

import javascript

/** Helper predicate to check whether xUnit.js is present. */
private predicate xUnitDetected() {
  // look for `Function.RegisterNamespace("xUnit.js");`
  exists (MethodCallExpr mc |
    mc.getParent() instanceof ExprStmt and
    mc.getReceiver().(GlobalVarAccess).getName() = "Function" and
    mc.getMethodName() = "RegisterNamespace" and
    mc.getNumArgument() = 1 and
    mc.getArgument(0).(StringLiteral).getValue() = "xUnit.js"
  )
}

/** Does `e` look like an xUnit.js attribute, possibly with arguments? */
private predicate possiblyAttribute(Expr e, string name) {
  exists (Identifier id | id = e or id = e.(CallExpr).getCallee() |
    name = id.getName() and
    name.regexpMatch("Async|Data|Fact|Fixture|Import|ImportJson|Skip|Trait")
  )
}

/**
 * Common abstraction for bracketed lists of expressions.
 *
 * Depending on their syntactic position, such lists will either be parsed as
 * array expressions, or as a property index expression where the indexing
 * expression is a comma expression: for example, in `[a, b][c, d]`, the
 * list `[a, b]` is an array expression, whereas `[c, d]` is an indexing
 * expression.
 *
 * We also allow singleton lists, as in `[a][b]`.
 */
abstract library class BracketedListOfExpressions extends Expr {
  abstract Expr getElement(int i);
}

library class ArrayExprIsABracketedListOfExpressions extends ArrayExpr, BracketedListOfExpressions {
  predicate isImpure() { ArrayExpr.super.isImpure() }
  Expr getElement(int i) { result = ArrayExpr.super.getElement(i) }
}

/**
 * A bracketed list of expressions that appears right after another such list,
 * and is hence parsed as an index expression.
 *
 * Note that the index expression itself does not include the opening and
 * closing brackets, for which we compensate by overriding `getFirstToken()`
 * and `getLastToken()`.
 */
library class IndexExprIndexIsBracketedListOfExpressions extends BracketedListOfExpressions {
  IndexExprIndexIsBracketedListOfExpressions() {
    exists (IndexExpr idx, Expr base |
      base = idx.getBase() and
      this = idx.getIndex() and
      // restrict to case where previous expression is also bracketed
      (base instanceof IndexExpr or base instanceof ArrayExpr)
    )
  }

  /**
   * If this is a sequence expression, delegate to the appropriate method of that class;
   * otherwise interpret as singleton list.
   */
  Expr getElement(int i) {
    result = this.(SeqExpr).getChildExpr(i) or
    not this instanceof SeqExpr and i  = 0 and result = this
  }

  /**
   * Override to include opening bracket.
   */
  Token getFirstToken() {
    result = BracketedListOfExpressions.super.getFirstToken().getPreviousToken()
  }

  /**
   * Override to include closing bracket.
   */
  Token getLastToken() {
    result = BracketedListOfExpressions.super.getLastToken().getNextToken()
  }
}

/**
 * Helper predicate: Does `ann` annotate `trg`, possibly skipping over other intervening
 * annotations?
 *
 * We use a token-level definition, since depending on the number of annotations involved
 * the AST structure can become pretty complicated.
 */
private predicate annotationTarget(BracketedListOfExpressions ann, XUnitTarget trg) {
  // every element looks like an attribute
  forex (Expr e | e = ann.getElement(_) | possiblyAttribute(e, _)) and
  // followed directly either by a target or by another annotation
  exists (Token next | next = ann.getLastToken().getNextToken() |
    trg.getFirstToken() = next or
    exists (BracketedListOfExpressions ann2 | ann2.getFirstToken() = next | annotationTarget(ann2, trg))
  )
}

/**
 * An xUnit.js annotation, such as `[Fixture]` or `[Data(23)]` annotating
 * a target declaration or definition.
 */
class XUnitAnnotation extends Expr {
  XUnitAnnotation() {
    xUnitDetected() and
    annotationTarget(this, _)
  }

  /** Get the declaration or definition to which this annotation belongs. */
  XUnitTarget getTarget() {
    annotationTarget(this, result)
  }

  /** Get the i-th attribute of this annotation. */
  Expr getAttribute(int i) {
    result = this.(BracketedListOfExpressions).getElement(i)
  }

  /** Get an attribute of this annotation. */
  Expr getAnAttribute() {
    result = getAttribute(_)
  }

  /** Get the number of attributes of this annotation. */
  int getNumAttribute() {
    result = strictcount(getAnAttribute())
  }

  /** Override to include brackets. */
  predicate hasLocationInfo(string path, int sl, int sc, int el, int ec) {
    exists (Location l1, Location l2 |
      l1 = getFirstToken().getLocation() and
      l2 = getLastToken().getLocation() |
      path = l1.getFile().getPath() and
      sl = l1.getStartLine() and
      sc = l1.getStartColumn() and
      el = l2.getEndLine() and
      ec = l2.getEndColumn()
    )
  }
}

/**
 * A declaration or definition that can serve as the target of an xUnit.js
 * annotation: a function declaration, a variable declaration, or an assignment.
 */
class XUnitTarget extends Stmt {
  XUnitTarget() {
    this instanceof FunctionDeclStmt or
    this instanceof VarDeclStmt or
    this.(ExprStmt).getExpr() instanceof AssignExpr
  }

  /** Get an annotation of which this is the target, if any. */
  XUnitAnnotation getAnAnnotation() {
    this = result.getTarget()
  }
}

/**
 * An xUnit.js attribute appearing in an annotation.
 */
class XUnitAttribute extends Expr {
  XUnitAttribute() {
    exists (XUnitAnnotation ann | this = ann.getAnAttribute())
  }

  /** Get the name of this attribute. */
  string getName() {
    possiblyAttribute(this, result)
  }

  /** Get the i-th parameter of this attribute. */
  Expr getParameter(int i) {
    result = this.(CallExpr).getArgument(i)
  }

  /** Get a parameter of this attribute. */
  Expr getAParameter() {
    result = getParameter(_)
  }

  /** Get the number of parameters of this attribute. */
  int getNumParameter() {
    result = count(getAParameter())
  }
}

/**
 * A function with an xUnit.js annotation.
 */
library class XUnitAnnotatedFunction extends Function {
  XUnitAnnotatedFunction() {
    exists (XUnitTarget target | exists(target.getAnAnnotation()) |
      this = target or
      this = target.(VarDeclStmt).getADecl().getInit() or
      this = target.(ExprStmt).getExpr().(AssignExpr).getRhs()
    )
  }

  /** Get an xUnit.js annotation on this function. */
  XUnitAnnotation getAnAnnotation() {
    result = this.(XUnitTarget).getAnAnnotation() or
    result = this.(Expr).getEnclosingStmt().(XUnitTarget).getAnAnnotation()
  }
}

/**
 * An xUnit.js `Fixture` annotation.
 */
class XUnitFixtureAnnotation extends XUnitAnnotation {
  XUnitFixtureAnnotation() {
    getAnAttribute().(GlobalVarAccess).getName() = "Fixture"
  }
}

/**
 * An xUnit.js fixture.
 */
class XUnitFixture extends XUnitAnnotatedFunction {
  XUnitFixture() {
    getAnAnnotation() instanceof XUnitFixtureAnnotation
  }
}

/**
 * An xUnit.js `Fact` annotation.
 */
class XUnitFactAnnotation extends XUnitAnnotation {
  XUnitFactAnnotation() {
    getAnAttribute().(GlobalVarAccess).getName() = "Fact"
  }
}

/**
 * An xUnit.js fact.
 */
class XUnitFact extends XUnitAnnotatedFunction {
  XUnitFact() {
    getAnAnnotation() instanceof XUnitFactAnnotation
  }
}