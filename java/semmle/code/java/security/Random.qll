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

predicate isSeeded(RValue use) {
  isSeeding(_, use)
  or
  exists(GetRandomData da, RValue seeduse |
    da.getQualifier() = seeduse and
    useUsePair(seeduse, use)
  )
}

predicate safelySeeded(RValue use) {
  exists(Expr arg |
    isSeeding(arg, use)
    and forall(FlowSource p | p.flowsToReverse(arg) | not p instanceof PredictableSeedExpr)
  )
  or
  exists(GetRandomData da, RValue seeduse |
    da.getQualifier() = seeduse and useUsePair(seeduse, use) |
    not exists(RValue prior | useUsePair(prior, seeduse) | isSeeded(prior))
  )
}

predicate unsafelySeeded(RValue use, PredictableSeedExpr source) {
  isSeedingSource(_, use, source) and
  not safelySeeded(use)
}

predicate isSeeding(Expr arg, RValue use) {
  exists(Expr e, VariableAssign def |
    def.getSource() = e and
    isSeedingConstruction(e, arg)
    |
    defUsePair(def, use) or
    def.getDestVar().(Field).getAnAccess() = use
  ) or
  exists(Expr e, RValue seeduse |
    e.(MethodAccess).getQualifier() = seeduse and
    isRandomSeeding(e, arg) and
    useUsePair(seeduse, use)
  )
}

predicate isSeedingSource(Expr arg, RValue use, FlowSource source) {
  isSeeding(arg, use) and
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
