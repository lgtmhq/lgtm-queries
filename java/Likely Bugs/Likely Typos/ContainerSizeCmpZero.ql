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
 * @name Container size compared to zero
 * @description Comparing the size of a container to zero with this operator will always return the same value.
 * @kind problem
 * @problem.severity warning
 * @tags reliability
 *       correctness
 *       logic
 */

import java
import semmle.code.java.Collections
import semmle.code.java.Maps

/** A union of the possible kinds of container size calls. */
abstract class SizeOfContainer extends Expr {
  abstract string getContainerKind();
}

/** A read access to the `length` field of an array. */
class ArrayLengthRead extends FieldRead, SizeOfContainer {
  ArrayLengthRead() {
    this.getField() instanceof ArrayLengthField
  }

  string toString() { result = FieldRead.super.toString() }
  string getContainerKind() { result = "an array" }
}

/** An access to `String.length()`. */
class StringLengthRead extends MethodAccess, SizeOfContainer {
  StringLengthRead() {
    this.getMethod() instanceof StringLengthMethod
  }

  Callable getEnclosingCallable() { result = MethodAccess.super.getEnclosingCallable() }
  Stmt getEnclosingStmt() { result = MethodAccess.super.getEnclosingStmt() }
  string toString() { result = MethodAccess.super.toString() }
  string getContainerKind() { result = "a string" }
}

/** An access to `Collection.size()`. */
class CollectionSizeCall extends MethodAccess, SizeOfContainer {
  CollectionSizeCall() {
      this.getMethod() instanceof CollectionSizeMethod
  }
  
  Callable getEnclosingCallable() { result = MethodAccess.super.getEnclosingCallable() }
  Stmt getEnclosingStmt() { result = MethodAccess.super.getEnclosingStmt() }
  string toString() { result = MethodAccess.super.toString() }
  string getContainerKind() { result = "a collection" }
}

/** An access to `Map.size()`. */
class MapSizeCall extends MethodAccess, SizeOfContainer {
  MapSizeCall() {
    this.getMethod() instanceof MapSizeMethod
  }

  Callable getEnclosingCallable() { result = MethodAccess.super.getEnclosingCallable() }
  Stmt getEnclosingStmt() { result = MethodAccess.super.getEnclosingStmt() }
  string toString() { result = MethodAccess.super.toString() }
  string getContainerKind() { result = "a map" }
}

class IntegralZeroLiteral extends Literal {
  IntegralZeroLiteral() {
    (this instanceof IntegerLiteral or this instanceof LongLiteral) and
    this.getLiteral().toInt() = 0
  }
}

private predicate comparisonOfContainerSizeToZero(BinaryExpr e, string containerKind, string trueOrFalse) {
  exists (Expr l, Expr r | l = e.getLeftOperand() and r = e.getRightOperand() |
    (e instanceof LTExpr and l.(SizeOfContainer).getContainerKind() = containerKind and
    r instanceof IntegralZeroLiteral and trueOrFalse = "false")
    or
    (e instanceof GTExpr and l instanceof IntegralZeroLiteral and
    r.(SizeOfContainer).getContainerKind() = containerKind and trueOrFalse = "false")
    or
    (e instanceof GEExpr and l.(SizeOfContainer).getContainerKind() = containerKind and
    r instanceof IntegralZeroLiteral and trueOrFalse = "true")
    or
    (e instanceof LEExpr and l instanceof IntegralZeroLiteral and
    r.(SizeOfContainer).getContainerKind() = containerKind and trueOrFalse = "true")
  )
}

from BinaryExpr e, string containerKind, string trueOrFalse
where comparisonOfContainerSizeToZero(e, containerKind, trueOrFalse)
select e, "This expression is always " + trueOrFalse + ", since " +
  containerKind + " can never have negative size."
