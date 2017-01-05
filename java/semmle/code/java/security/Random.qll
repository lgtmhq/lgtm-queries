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

import java
import semmle.code.java.security.DataFlow

class SecureRandomNumberGenerator extends RefType {
  SecureRandomNumberGenerator() {
    this.hasQualifiedName("java.security", "SecureRandom")
  }
}

class GetRandomData extends MethodAccess {
  GetRandomData() {
    this.getMethod().getName().matches("next%") and
    this.getQualifier().getType() instanceof SecureRandomNumberGenerator
  }
}

predicate isSeeded(Stmt s, Variable v) {
  exists(Stmt pred | isSeeded(pred, v) | pred.getASuccessor() = s)
  or
  exists(Expr e | e.getEnclosingStmt() = s | 
    isSeeding(v, e, _)
    or
    e.(GetRandomData).getQualifier() = v.getAnAccess()
  )
}

predicate safelySeeded(Stmt s, Variable v) {
  exists(Stmt pred | safelySeeded(pred, v) | pred.getASuccessor() = s)
  or
  exists(Expr e, Expr arg | e.getEnclosingStmt() = s |
    isSeeding(v, e, arg)
    and forall(FlowSource p | p.flowsToReverse(arg) | not p instanceof PredictableSeedExpr)
  )
  or
  exists(GetRandomData da |
    da.getQualifier() = v.getAnAccess() and da.getEnclosingStmt() = s |
    not exists(Stmt pred | pred.getASuccessor() = s | isSeeded(pred, v))
  )
}

predicate unsafelySeeded(Stmt s, Variable v, PredictableSeedExpr source) {
  exists(Expr e | isSeedingSource(v, e, _, source) and e.getEnclosingStmt().getASuccessor*() = s) and
  not safelySeeded(s, v)
}

predicate isSeeding(Variable v, Expr e, Expr arg) {
  (e = v.getAnAssignedValue() and isSeedingConstruction(e, arg)) or
  (e.(MethodAccess).getQualifier() = v.getAnAccess() and isRandomSeeding(e, arg))
}

predicate isSeedingSource(Variable v, Expr e, Expr arg, FlowSource source) {
  isSeeding(v, e, arg) and
  source.flowsToReverse(arg)
}

predicate isRandomSeeding(MethodAccess m, Expr arg) {
  exists(Method def | 
    m.getMethod() = def | 
    def.getDeclaringType() instanceof SecureRandomNumberGenerator 
    and def.getName() = "setSeed" 
    and arg = m.getArgument(0)
  )
}

predicate isSeedingConstruction(ClassInstanceExpr c, Expr arg) {
  c.getConstructedType() instanceof SecureRandomNumberGenerator
  and
  c.getNumArgument() = 1
  and
  c.getArgument(0) = arg
}

class PredictableSeedExpr extends FlowSource {
  PredictableSeedExpr() {
    this.(MethodAccess).getCallee() instanceof ReturnsPredictableExpr or
    this instanceof CompileTimeConstantExpr
  }
}

abstract class ReturnsPredictableExpr extends Method {}

class ReturnsSystemTime extends ReturnsPredictableExpr {
  ReturnsSystemTime() {
    (this.getDeclaringType().hasQualifiedName("java.lang", "System") and this.hasName("currentTimeMillis")) or
    (this.getDeclaringType().hasQualifiedName("java.lang", "System") and this.hasName("nanoTime"))
  }
}
