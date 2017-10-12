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

/** Provides classes for working with ECMAScript 2015 modules. */

import Stmt
import Modules

/**
 * An ECMAScript 2015 module.
 */
class ES2015Module extends Module {
  ES2015Module() {
    isModule(this) and
    not isNodejs(this)
  }

  override ModuleScope getScope() {
    result.getScopeElement() = this
  }

  /** Gets the full path of the file containing this module. */
  override string getPath() {
    result = getFile().getAbsolutePath()
  }

  /** Gets the short name of this module without file extension. */
  override string getName() {
    result = getFile().getStem()
  }

  /** Gets an import declaration in this module. */
  ImportDeclaration getAnImport() {
    result.getTopLevel() = this
  }

  /** Gets an export declaration in this module. */
  ExportDeclaration getAnExport() {
    result.getTopLevel() = this
  }

  override Module getAnImportedModule() {
    result = getAnImport().getImportedModule()
  }

  override predicate exports(string name, ASTNode export) {
    exists (ExportDeclaration ed |
      ed = getAnExport() and ed = export |
      ed.exportsAs(_, name)
    )
  }

  /** Holds if this module exports variable `v` under the name `name`. */
  predicate exportsAs(Variable v, string name) {
    getAnExport().exportsAs(v, name)
  }

  override predicate isStrict() {
    // modules are implicitly strict
    any()
  }
}

/** An import declaration. */
class ImportDeclaration extends Stmt, Import, @importdeclaration {
  override ES2015Module getEnclosingModule() {
    this = result.getAnImport()
  }

  override PathExprInModule getImportedPath() {
    result = getChildExpr(-1)
  }

  /** Gets the `i`th import specifier of this import declaration. */
  ImportSpecifier getSpecifier(int i) {
    result = getChildExpr(i)
  }

  /** Gets an import specifier of this import declaration. */
  ImportSpecifier getASpecifier() {
    result = getSpecifier(_)
  }
}

/** A literal path expression appearing in an `import` declaration. */
private class LiteralImportPath extends PathExprInModule, @stringliteral {
  LiteralImportPath() {
    exists (ImportDeclaration req | this = req.getChildExpr(-1))
  }

  override string getValue() { result = this.(StringLiteral).getValue() }
}

/**
 * An import specifier in an import declaration.
 *
 * There are four kinds of import specifiers:
 *
 *   - default import specifiers, which import the default export of a module
 *     and make it available under a local name, as in `import` <u>`f`</u> `from 'a'`;
 *   - namespace import specifiers, which import all exports of a module and
 *     make them available through a local namespace object, as in
 *     `import` <u>`* as ns`</u> `from 'a'`;
 *   - named import specifiers, which import a named export of a module and
 *     make it available in the importing module under the same name, as in
 *     `import {` <u>`x`</u> `} from 'a'`;
 *   - renaming import specifiers, which import a named export of a module and
 *     make it available in the importing module under a different name, as in
 *     `import {` <u>`x as y`</u> `} from 'a'`.
 * */
class ImportSpecifier extends Expr, @importspecifier {
  /** Gets the imported symbol; undefined for default and namespace import specifiers. */
  Identifier getImported() {
    result = getChildExpr(0)
  }

  /**
   * Gets the name of the imported symbol.
   *
   * For example, consider these four imports:
   *
   * ```javascript
   * import { x } from 'a'
   * import { y as z } from 'b'
   * import f from 'c'
   * import * as g from 'd'
   * ```
   *
   * The names of the imported symbols for the first three of them are, respectively,
   * `x`, `y` and `default`, while the last one does not import an individual symbol.
   */
  string getImportedName() {
    result = getImported().getName()
  }

  /** Gets the local variable into which this specifier imports. */
  VarDecl getLocal() {
    result = getChildExpr(1)
  }
}

/** A named import specifier. */
class NamedImportSpecifier extends ImportSpecifier, @namedimportspecifier {
}

/** A default import specifier. */
class ImportDefaultSpecifier extends ImportSpecifier, @importdefaultspecifier {
  override string getImportedName() {
    result = "default"
  }
}

/** A namespace import specifier. */
class ImportNamespaceSpecifier extends ImportSpecifier, @importnamespacespecifier {
}

/** A bulk import that imports an entire module as a namespace. */
class BulkImportDeclaration extends ImportDeclaration {
  BulkImportDeclaration() {
    getASpecifier() instanceof ImportNamespaceSpecifier
  }

  /** Gets the local namespace variable under which the module is imported. */
  VarDecl getLocal() {
    result = getASpecifier().getLocal()
  }
}

/** A selective import that imports zero or more declarations. */
class SelectiveImportDeclaration extends ImportDeclaration {
  SelectiveImportDeclaration() {
    not this instanceof BulkImportDeclaration
  }

  /** Holds if `local` is the local variable into which `imported` is imported. */
  predicate importsAs(string imported, VarDecl local) {
    exists (ImportSpecifier spec | spec = getASpecifier() |
      imported = spec.getImported().getName() and
      local = spec.getLocal()
    ) or
    imported = "default" and local = getASpecifier().(ImportDefaultSpecifier).getLocal()
  }
}

/**
 * An export declaration.
 *
 * There are three kinds of export declarations:
 *
 *   - a bulk re-export declaration of the form `export * from 'a'`, which re-exports
 *     all exports of another module;
 *   - a default export declaration of the form `export default var x = 42`, which exports
 *     a local value or declaration as the default export;
 *   - a named export declaration such as `export { x, y as z }`, which exports local
 *     values or declarations under specific names; a named export declaration
 *     may also export symbols itself imported from another module, as in
 *     `export { x } from 'a'`.
 */
abstract class ExportDeclaration extends Stmt, @exportdeclaration {
  /** Gets the module to which this export declaration belongs. */
  ES2015Module getEnclosingModule() {
    this = result.getAnExport()
  }

  /** Holds if this export declaration exports variable `v` under the name `name`. */
  abstract predicate exportsAs(Variable v, string name);

  /**
   * Gets the data flow node corresponding to the value this declaration exports
   * under the name `name`.
   *
   * For example, consider the following exports:
   *
   * ```javascript
   * export var x = 23;
   * export { y as z };
   * export default function f() { ... };
   * export { x } from 'a';
   * ```
   *
   * The first one exports `23` under the name `x`, the second one exports
   * `y` under the name `z`, while the third one exports `function f() { ... }`
   * under the name `default`.
   *
   * The final export re-exports under the name `x` whatever module `a`
   * exports under the same name. In particular, its source node belongs
   * to module `a` or possibly to some other module from which `a` re-exports.
   */
  abstract DataFlowNode getSourceNode(string name);
}

/**
 * A bulk re-export declaration of the form `export * from 'a'`, which re-exports
 * all exports of another module.
 */
class BulkReExportDeclaration extends ReExportDeclaration, @exportalldeclaration {
  /** Gets the name of the module from which this declaration re-exports. */
  override StringLiteral getImportedPath() {
    result = getChildExpr(0)
  }

  override predicate exportsAs(Variable v, string name) {
    getImportedModule().exportsAs(v, name)
  }

  override DataFlowNode getSourceNode(string name) {
    result = getImportedModule().getAnExport().getSourceNode(name)
  }
}

/**
 * A default export declaration such as `export default function f{}`
 * or `export default { x: 42 }`.
 */
class ExportDefaultDeclaration extends ExportDeclaration, @exportdefaultdeclaration {
  /** Gets the operand statement or expression that is exported by this declaration. */
  ExprOrStmt getOperand() {
    result = getChild(0)
  }

  override predicate exportsAs(Variable v, string name) {
    name = "default" and v = getADecl().getVariable()
  }

  /** Gets the declaration, if any, exported by this default export. */
  VarDecl getADecl() {
    exists (ExprOrStmt op | op = getOperand() |
      result = op.(FunctionDeclStmt).getId() or
      result = op.(ClassDeclStmt).getIdentifier()
    )
  }

  override DataFlowNode getSourceNode(string name) {
    name = "default" and result = getOperand()
  }
}

/** A named export declaration such as `export { x, y }` or `export var x = 42`. */
class ExportNamedDeclaration extends ExportDeclaration, @exportnameddeclaration {
  /** Gets the operand statement or expression that is exported by this declaration. */
  ExprOrStmt getOperand() {
    result = getChild(-1)
  }

  /** Gets the declaration, if any, exported by this named export. */
  VarDecl getADecl() {
    exists (ExprOrStmt op | op = getOperand() |
      result = op.(DeclStmt).getADecl().getBindingPattern().getABindingVarRef() or
      result = op.(FunctionDeclStmt).getId() or
      result = op.(ClassDeclStmt).getIdentifier() or
      result = op.(NamespaceDeclaration).getId()
    )
  }

  override predicate exportsAs(Variable v, string name) {
    exists (VarDecl vd | vd = getADecl() | name = vd.getName() and v = vd.getVariable()) or
    exists (ExportSpecifier spec | spec = getASpecifier() |
      name = spec.getExported().getName() and
      (v = spec.getLocal().(VarAccess).getVariable() or
       this.(ReExportDeclaration).getImportedModule().exportsAs(v, spec.getLocal().getName()))
    )
  }

  override DataFlowNode getSourceNode(string name) {
    exists (VarDef d | d.getTarget() = getADecl() |
      name = d.getTarget().(VarDecl).getName() and
      result = d.getSource()
    ) or
    exists (ExportSpecifier spec | spec = getASpecifier() and name = spec.getExported().getName() |
      not exists(getImportedPath()) and result = spec.getLocal()
      or
      exists (ReExportDeclaration red | red = this |
        result = red.getImportedModule().getAnExport().getSourceNode(spec.getLocal().getName())
      )
    )
  }

  /** Gets the module from which the exports are taken if this is a re-export. */
  StringLiteral getImportedPath() {
    result = getChildExpr(-2)
  }

  /** Gets the `i`th export specifier of this declaration. */
  ExportSpecifier getSpecifier(int i) {
    result = getChildExpr(i)
  }

  /** Gets an export specifier of this declaration. */
  ExportSpecifier getASpecifier() {
    result = getSpecifier(_)
  }
  
  override predicate isAmbient() {
    // An export such as `export declare function f()` should be seen as ambient.
    hasDeclareKeyword(getOperand()) or getParent().isAmbient()
  }
}

/** An export specifier in a named export declaration. */
class ExportSpecifier extends Expr, @exportspecifier {
  /** Gets the local symbol that is being exported. */
  Identifier getLocal() {
    result = getChildExpr(0)
  }

  /** Gets the name under which the symbol is exported. */
  Identifier getExported() {
    result = getChildExpr(1)
  }
}

/** A named export specifier. */
class NamedExportSpecifier extends ExportSpecifier, @namedexportspecifier {
}

/** A default export specifier. */
class ExportDefaultSpecifier extends ExportSpecifier, @exportdefaultspecifier {
}

/** A namespace export specifier. */
class ExportNamespaceSpecifier extends ExportSpecifier, @exportnamespacespecifier {
}

/** An export declaration that re-exports declarations from another module. */
abstract class ReExportDeclaration extends ExportDeclaration {
  /** Gets the path of the module from which this declaration re-exports. */
  abstract StringLiteral getImportedPath();

  /** Gets the module from which this declaration re-exports. */
  ES2015Module getImportedModule() {
    result.getFile() = getEnclosingModule().resolve(getImportedPath().(PathExpr))
  }
}

/** A literal path expression appearing in a re-export declaration. */
private class LiteralReExportPath extends PathExprInModule, @stringliteral {
  LiteralReExportPath() {
    exists (ReExportDeclaration bred | this = bred.getImportedPath())
  }

  override string getValue() { result = this.(StringLiteral).getValue() }
}

/** A named export declaration that re-exports symbols imported from another module. */
class SelectiveReExportDeclaration extends ReExportDeclaration, ExportNamedDeclaration {
  SelectiveReExportDeclaration() {
    exists(ExportNamedDeclaration.super.getImportedPath())
  }

  /** Gets the path of the module from which this declaration re-exports. */
  override StringLiteral getImportedPath() { result = ExportNamedDeclaration.super.getImportedPath() }
}

/** An export declaration that exports zero or more declarations from the module it appears in. */
class OriginalExportDeclaration extends ExportDeclaration {
  OriginalExportDeclaration() {
    not this instanceof ReExportDeclaration
  }

  override predicate exportsAs(Variable v, string name) {
    this.(ExportDefaultDeclaration).exportsAs(v, name) or
    this.(ExportNamedDeclaration).exportsAs(v, name)
  }

  override DataFlowNode getSourceNode(string name) {
    result = this.(ExportDefaultDeclaration).getSourceNode(name) or
    result = this.(ExportNamedDeclaration).getSourceNode(name)
  }
}
