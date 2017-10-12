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

import javascript

/** A TypeScript namespace declaration. */
class NamespaceDeclaration extends Stmt, StmtContainer, @namespacedeclaration {
  /** Gets the name of this namespace. */
  Identifier getId() {
    result = getChild(-1)
  }

  /** Gets the `i`th statement in this namespace. */
  Stmt getStmt(int i) {
    i >= 0 and
    result = getChild(i)
  }

  /** Gets a statement in this namespace. */
  Stmt getAStmt() {
    result = getStmt(_)
  }

  /** Gets the number of statements in this namespace. */
  int getNumStmt() {
    result = count(getAStmt())
  }

  override StmtContainer getEnclosingContainer() { result = this.getContainer() }

  /**
   * Holds if this declaration implies the existence of a concrete namespace object at runtime.
   *
   * A namespace that is empty or only contains interfaces and type aliases is not instantiated,
   * and thus has no namespace object at runtime and is not associated with a variable.
   */
  predicate isInstantiated() {
    isInstantiated(this)
  }
}

/** A TypeScript "import-equals" declaration. */
class ImportEqualsDeclaration extends Stmt, @importequalsdeclaration {
  /** Gets the name under which the imported entity is imported. */
  Identifier getId() {
    result = getChild(0)
  }

  /** Gets the expression specifying the imported module or entity. */
  Expr getImportedEntity() {
    result = getChild(1)
  }
}

/** A TypeScript external module reference. */
class ExternalModuleReference extends Expr, Import, @externalmodulereference {
  /** Gets the expression specifying the module. */
  Expr getExpression() {
    result = getChild(0)
  }

  override PathExpr getImportedPath() {
    result = getExpression()
  }

  override Module getEnclosingModule() {
    result = getTopLevel()
  }

  override ControlFlowNode getFirstControlFlowNode() {
    result = getExpression().getFirstControlFlowNode()
  }
}

/** A literal path expression appearing in an external module reference. */
private class LiteralExternalModulePath extends PathExprInModule, @stringliteral {
  LiteralExternalModulePath() {
    exists (ExternalModuleReference emr | this.getParentExpr*() = emr.getExpression())
  }

  override string getValue() { result = this.(StringLiteral).getValue() }
}

/** A TypeScript "export-assign" declaration. */
class ExportAssignDeclaration extends Stmt, @exportassigndeclaration {
  /** Gets the expression exported by this declaration. */
  Expr getExpression() {
    result = getChild(0)
  }
}
