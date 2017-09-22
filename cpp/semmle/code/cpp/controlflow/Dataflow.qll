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

import default
import Nullness
import Dereferenced

abstract class DataflowAnnotation extends string {
  DataflowAnnotation() { this = "pointer-null" or this = "pointer-valid" }

  abstract predicate isDefault();
  abstract predicate generatedOn(Expr e);
  abstract predicate generatedBy(LocalScopeVariable v, ControlFlowNode src, ControlFlowNode dest);
  abstract predicate killedBy(LocalScopeVariable v, ControlFlowNode src, ControlFlowNode dest);

  predicate marks(Expr e) {
    (this.generatedOn(e) and reachable(e))
    or
    this.marks(e.(AssignExpr).getRValue())
    or
    exists(LocalScopeVariable v | this.marks(v, e) and e = v.getAnAccess())
  }

  predicate marks(LocalScopeVariable v, ControlFlowNode n) {
    (
      v.getAnAccess().getEnclosingFunction().getBlock() = n and
      this.isDefault()
    )
    or
    (
      this.marks(n.(Initializer).getExpr()) and
      v.getInitializer() = n
    )
    or
    exists(ControlFlowNode pred |
      this.generatedBy(v, pred, n)
      and not this.killedBy(v, pred, n)
      and reachable(pred)
    )
    or
    exists(ControlFlowNode pred |
      this.assignedBy(v, pred, n)
      and not this.killedBy(v, pred, n)
      and reachable(pred)
    )
    or
    exists(ControlFlowNode pred |
      this.preservedBy(v, pred, n)
      and not this.killedBy(v, pred, n)
      and reachable(pred)
    )
  }

  predicate preservedBy(LocalScopeVariable v, ControlFlowNode src, ControlFlowNode dest) {
    this.marks(v, src) and
    src.getASuccessor() = dest and
    not v.getInitializer() = dest and
    not v.getAnAssignment() = src
  }

  predicate assignedBy(LocalScopeVariable v, ControlFlowNode src, ControlFlowNode dest) {
    this.marks(src.(AssignExpr).getRValue()) and
    src = v.getAnAssignment() and
    src.getASuccessor() = dest
  }
}

class NullnessAnnotation extends DataflowAnnotation {
  NullnessAnnotation() { this = "pointer-null" or this = "pointer-valid" }

  predicate isDefault() { this = "pointer-valid" }

  predicate generatedOn(Expr e) {
    exists(Variable v |
      v.getAnAccess() = e and
      (v instanceof GlobalVariable or v instanceof Field) and
      this.isDefault())
    or
    (e instanceof Call and this = "pointer-valid")
    or
    (nullValue(e) and this = "pointer-null")
  }

  predicate killedBy(LocalScopeVariable v, ControlFlowNode src, ControlFlowNode dest) {
    (((AnalysedExpr) src).getNullSuccessor(v) = dest and this = "pointer-valid")
    or
    (((AnalysedExpr) src).getNonNullSuccessor(v) = dest and this = "pointer-null")
    or
    (dest = src.getASuccessor() and callByReference(src, v) and not this.isDefault())
    or
    (dest = src.getASuccessor()
      and deref(v, src)
      and this = "pointer-null")
  }

  predicate generatedBy(LocalScopeVariable v, ControlFlowNode src, ControlFlowNode dest) {
    dest = src.getASuccessor() and
    callByReference(src, v) and
    this.isDefault()
  }
}

predicate deref(Variable v, Expr op) {
  dereferencedByOperation(op, v.getAnAccess())
}

predicate callByReference(Call call, Variable v) {
  exists(Expr arg |
    call.getAnArgument() = arg and
    (
      ((AddressOfExpr) arg).getAChild() = v.getAnAccess()
      or
      (v.getAnAccess() = arg and arg.getConversion*() instanceof ReferenceToExpr)
    )
  )
}

predicate definitelyNull(Expr e) {
  ((NullnessAnnotation) "pointer-null").marks(e)
  and
  not ((NullnessAnnotation) "pointer-valid").marks(e)
}

predicate maybeNull(Expr e) {
  ((NullnessAnnotation) "pointer-null").marks(e)
}
