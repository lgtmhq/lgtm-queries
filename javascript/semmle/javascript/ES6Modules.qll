// Copyright 2016 Semmle Ltd.
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

import Stmt
import Modules

/**
 * An ECMAScript 6 module.
 */
class ES6Module extends Module {
  ES6Module() {
    exists (ModuleScope ms | ms.getScopeElement() = this) and
    not isNodejs(this)
  }
  
  /** The scope induced by this module. */
  ModuleScope getScope() {
    result.getScopeElement() = this
  }
  
  /** The full path of the file containing this module. */
  string getPath() {
    result = getFile().getPath()
  }
  
  /** The short name of this module without file extension. */
  string getName() {
    exists (string basename, string ext |
      basename = getFile().getName() and
      ext = getFile().getExtension() and
      result = basename.substring(0, basename.length()-ext.length()-1)
    )
  }

  /** Get an import declaration in this module. */
  ImportDeclaration getAnImport() {
    result.getTopLevel() = this
  }

  /** Get an export declaration in this module. */
  ExportDeclaration getAnExport() {
    result.getTopLevel() = this
  }

  Module getAnImportedModule() {
    result = getAnImport().getImportedModule()
  }

  predicate exports(string name, ASTNode export) {
    exists (ExportDeclaration ed |
      ed = getAnExport() and ed = export |
      ed.exportsAs(_, name)
    )
  }

  /** Does this module export variable `v` under the name `name`? */
  predicate exportsAs(Variable v, string name) {
    getAnExport().exportsAs(v, name)
  }

  predicate isStrict() {
    // modules are implicitly strict
    any()
  }
}

/** An import declaration. */
class ImportDeclaration extends Stmt, Import, @importdeclaration {
  ES6Module getEnclosingModule() {
    this = result.getAnImport()
  }

  PathExpr getImportedPath() {
    result = getChildExpr(-1)
  }

  ES6Module getImportedModule() {
    result.getFile() = getEnclosingModule().resolve(getImportedPath().(PathExpr))
  }

  /** Get the i-th import specifier of this import declaration. */
  ImportSpecifier getSpecifier(int i) {
    result = getChildExpr(i)
  }

  /** Get some import specifier of this import declaration. */
  ImportSpecifier getASpecifier() {
    result = getSpecifier(_)
  }

  string toString() { result = Stmt.super.toString() }
}

/** A literal path expression appearing in an <code>import</code> declaration. */
library class LiteralImportPath extends PathExpr, StringLiteral {
  LiteralImportPath() {
    exists (ImportDeclaration req | this = req.getChildExpr(-1))
  }

  string getValue() { result = StringLiteral.super.getValue() }
  predicate isImpure() { StringLiteral.super.isImpure() }
  string getStringValue() { result = StringLiteral.super.getStringValue() }
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
  /** Get the imported symbol; undefined for default and namespace import specifiers. */
  Identifier getImported() {
    result = getChildExpr(0)
  }

  /** Get the local variable into which this specifier imports. */
  VarDecl getLocal() {
    result = getChildExpr(1)
  }
}

/** A named import specifier. */
class NamedImportSpecifier extends ImportSpecifier, @namedimportspecifier {
}

/** A default import specifier. */
class ImportDefaultSpecifier extends ImportSpecifier, @importdefaultspecifier {
}

/** A namespace import specifier. */
class ImportNamespaceSpecifier extends ImportSpecifier, @importnamespacespecifier {
}

/** A bulk import that imports an entire module as a namespace. */
class BulkImportDeclaration extends ImportDeclaration {
  BulkImportDeclaration() {
    getASpecifier() instanceof ImportNamespaceSpecifier
  }

  /** Get the local namespace variable under which the module is imported. */
  VarDecl getLocal() {
    result = getASpecifier().getLocal()
  }
}

/** A selective import that imports zero or more declarations. */
class SelectiveImportDeclaration extends ImportDeclaration {
  SelectiveImportDeclaration() {
    not this instanceof BulkImportDeclaration
  }

  /** Bind `local` to the local variable into which `imported` is imported. */
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
  /** Get the module to which this export declaration belongs. */
  ES6Module getEnclosingModule() {
    this = result.getAnExport()
  }

  /** Does this export declaration export variable `v` under the name `name`? */
  abstract predicate exportsAs(Variable v, string name);
}

/** 
 * A bulk re-export declaration of the form `export * from 'a'`, which re-exports
 * all exports of another module.
 */
class BulkReExportDeclaration extends ReExportDeclaration, @exportalldeclaration {
  /** Get the name of the module from which this declaration re-exports. */
  StringLiteral getImportedPath() {
    result = getChildExpr(0)
  }

  predicate exportsAs(Variable v, string name) {
    getImportedModule().exportsAs(v, name)
  }
}

/** A default export declaration such as `export default var x = 42`. */
class ExportDefaultDeclaration extends ExportDeclaration, @exportdefaultdeclaration {
  /** Get the operand statement or expression that is exported by this declaration. */
  ExprOrStmt getOperand() {
    result = getChild(0)
  }

  predicate exportsAs(Variable v, string name) {
    name = "default" and v = getADecl().getVariable()
  }

  /** Get the declaration, if any, exported by this default export. */
  VarDecl getADecl() {
    exists (ExprOrStmt op | op = getOperand() |
      result = op.(DeclStmt).getADecl().getBindingPattern().getABindingVarRef() or
      result = op.(FunctionDeclStmt).getId() or
      result = op.(ClassDeclStmt).getIdentifier()
    )
  }
}

/** A named export declaration such as `export { x, y }` or `export var x = 42`. */
class ExportNamedDeclaration extends ExportDeclaration, @exportnameddeclaration {
  /** Get the operand statement or expression that is exported by this declaration. */
  ExprOrStmt getOperand() {
    result = getChild(-1)
  }

  /** Get the declaration, if any, exported by this named export. */
  VarDecl getADecl() {
    exists (ExprOrStmt op | op = getOperand() |
      result = op.(DeclStmt).getADecl().getBindingPattern().getABindingVarRef() or
      result = op.(FunctionDeclStmt).getId() or
      result = op.(ClassDeclStmt).getIdentifier()
    )
  }

  predicate exportsAs(Variable v, string name) {
    exists (VarDecl vd | vd = getADecl() | name = vd.getName() and v = vd.getVariable()) or
    exists (ExportSpecifier spec | spec = getASpecifier() |
      name = spec.getExported().getName() and
      (v = spec.getLocal().(VarAccess).getVariable() or
       this.(ReExportDeclaration).getImportedModule().exportsAs(v, spec.getLocal().getName()))
    )
  }

  /** If this is a re-export, get the module from which the exports are taken. */
  StringLiteral getImportedPath() {
    result = getChildExpr(-2)
  }

  /** Get the i-th export specifier of this declaration. */
  ExportSpecifier getSpecifier(int i) {
    result = getChildExpr(i)
  }

  /** Get some export specifier of this declaration. */
  ExportSpecifier getASpecifier() {
    result = getSpecifier(_)
  }
}

/** An export specifier in a named export declaration. */
class ExportSpecifier extends Expr, @exportspecifier {
  /** Get the local symbol that is being exported. */
  Identifier getLocal() {
    result = getChildExpr(0)
  }

  /** Get the name under which the symbol is exported. */
  Identifier getExported() {
    result = getChildExpr(1)
  }
}

/** An export declaration that re-exports declarations from another module. */
abstract class ReExportDeclaration extends ExportDeclaration {
  /** Get the path of the module from which this declaration re-exports. */
  abstract StringLiteral getImportedPath();

  /** Get the module from which this declaration re-exports. */
  ES6Module getImportedModule() {
    result.getFile() = getEnclosingModule().resolve(getImportedPath().(PathExpr))
  }
}

/** A literal path expression appearing in a re-export declaration. */
library class LiteralReExportPath extends PathExpr, StringLiteral {
  LiteralReExportPath() {
    exists (ReExportDeclaration bred | this = bred.getImportedPath())
  }

  string getValue() { result = StringLiteral.super.getValue() }
  predicate isImpure() { StringLiteral.super.isImpure() }
  string getStringValue() { result = StringLiteral.super.getStringValue() }
}

/** A named export declaration that re-exports symbols imported from another module. */
class SelectiveReExportDeclaration extends ReExportDeclaration, ExportNamedDeclaration {
  SelectiveReExportDeclaration() {
    exists(ExportNamedDeclaration.super.getImportedPath())
  }

  /** Get the path of the module from which this declaration re-exports. */
  StringLiteral getImportedPath() { result = ExportNamedDeclaration.super.getImportedPath() }
}

/** An export declaration that exports zero or more declarations from the module it appears in. */
class OriginalExportDeclaration extends ExportDeclaration {
  OriginalExportDeclaration() {
    not this instanceof ReExportDeclaration
  }

  predicate exportsAs(Variable v, string name) {
    this.(ExportDefaultDeclaration).exportsAs(v, name) or
    this.(ExportNamedDeclaration).exportsAs(v, name)
  }
}
