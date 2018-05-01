// Copyright 2018 Semmle Ltd.
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
 * Provides classes for working with name resolution of namespaces and types.
 */

import javascript

/**
 * Holds if `decl` is the immediate operand to an export declaration, such as:
 * ```
 * export namespace X {}
 * ```
 *
 * Does *not* consider declarations that are exported by name, for example:
 * ```
 * namespace X {} // not an "exported statement"
 * export {X}
 * ```
 */
private predicate isExportedStmt(Stmt stmt) {
  exists (ExportNamedDeclaration decl | decl.getOperand() = stmt)
  or
  // ambient namespaces implicitly export their members
  stmt.getContainer().(NamespaceDeclaration).isAmbient()
  or
  stmt.getContainer().(ExternalModuleDeclaration).isAmbient()
}

/**
 * The canonical name of a namespace, underlying the `Namespace` type.
 */
private newtype TNamespace =
  /** The root namespace of a module, containing its exported members. */
  TNamespaceModuleRoot(Module mod) {
    not exists (getExternalModuleName(mod.getFile()))
  }
  or
  /** A namespace defined locally. */
  TNamespaceLexicalRoot(LocalNamespaceName local) {
    exists (NamespaceDefinition def |
      def.getId().(LocalNamespaceDecl).getLocalNamespaceName() = local and
      not isExportedStmt(def))
  }
  or
  /** A namespace exported from an enclosing namespace. */
  TNamespaceMember(TNamespace parent, string name) {
    exists (NamespaceDefinition def |
      isExportedStmt(def) and
      parent = getExportNamespace(def.getContainer()) and
      name = def.getName())
  }
  or
  /** A namespace induced by a an external module declaration, such as `declare module "X" {}`. */
  TExternalModule(string name) {
    name = any(ExternalModuleDeclaration decl).getName()
    or
    name = getExternalModuleName(_)
  }

/** Gets the namespace to which `export` statements in the given container should contribute. */
private TNamespace getExportNamespace(StmtContainer container) {
  exists (Module mod | container = mod |
    result = TNamespaceModuleRoot(mod))
  or
  exists (NamespaceDeclaration decl | container = decl |
    if hasReassignedExportTarget(decl) then
      result = getReassignedExportTarget(decl)
    else if isExportedStmt(decl) then
      result = TNamespaceMember(getExportNamespace(decl.getEnclosingContainer()), decl.getName())
    else
      result = TNamespaceLexicalRoot(decl.getLocalNamespaceName()))
  or
  exists (ExternalModuleDeclaration decl | container = decl |
    result = TExternalModule(decl.getName()))
  or
  result = TExternalModule(getExternalModuleName(container.(Module).getFile()))
}

/**
 * If the given namespace is the target of an export-assign declaration, gets the container of
 * the export-assign.
 *
 * This is often used to export the contents of a namespace in the enclosing module:
 * ```
 * export = MyLib
 * declare namespace MyLib {}
 * ```
 *
 * It is also used inside an external module declaration to export the contents
 * of a proper namespace:
 * ```
 * declare namespace __MyLib {
 *   interface I {...}
 * }
 * declare module "myLib" {
 *   export = __MyLib;
 * }
 * ```
 *
 * This differs from a re-export in that declarations can be extended afterwards.
 * Continuing the previous example:
 * ```
 * declare module "myLib" {
 *   interface I {..} // extends previous definition of I
 * }
 * ```
 * For this to work, the canonical name for `I` must be based on the external module
 * `"myLib"`, as opposed to `__MyLib`.
 */
private Namespace getReassignedExportTarget(NamespaceDeclaration decl) {
  exists (ExportAssignDeclaration exprt |
    exprt.getExpression().(ExportVarAccess).getLocalNamespaceName() = decl.getLocalNamespaceName() and
    result = getExportNamespace(exprt.getContainer()))
}

/**
 * Like `exists(getReassignedExportTarget(decl))` but is not recursive.
 */
private predicate hasReassignedExportTarget(NamespaceDeclaration decl) {
  exists (ExportAssignDeclaration exprt |
    exprt.getExpression().(ExportVarAccess).getLocalNamespaceName() = decl.getLocalNamespaceName())
}

/**
 * Gets the name of the external module for which the given file is an interface file, if any.
 */
private string getExternalModuleName(File file) {
  exists (Folder nodeModules |
    nodeModules.getBaseName() = "node_modules" and
    nodeModules.getFolder("@types").getFolder(result).getFile("index.d.ts") = file)
}

/**
 * The canonical name of a namespace, representing a module or TypeScript namespace declaration.
 */
class Namespace extends TNamespace {
  /** Gets the unqualified name of this namespace, or the file name it is the root namespace of a module. */
  string getName() {
    exists (Module mod | this = TNamespaceModuleRoot(mod) | result = describeRootScope(mod.getScope()))
    or
    exists (LocalNamespaceName local | this = TNamespaceLexicalRoot(local) | result = local.getName())
    or
    this = TNamespaceMember(_, result)
    or
    this = TExternalModule(result)
  }

  /** Gets the enclosing namespace, if any. */
  Namespace getParent() {
    this = TNamespaceMember(result, _)
  }

  /** Gets a namespace nested in this one. */
  Namespace getNamespaceMember(string name) {
    // Extend the canonical name if inner namespace exists, e.g. lookup(`A.B`, `C`) => `A.B.C`
    result = TNamespaceMember(this, name)
    or
    // Look for aliased members, e.g. lookup(`A.B`, `C`) => `Q.W`
    result = NameResolution::getAliasedNamespaceMember(this, name)
  }

  /** Gets the type of the given name in this namespace, if any. */
  TypeName getTypeMember(string name) {
    result = TExportedTypeName(this, name)
    or
    result = NameResolution::getAliasedTypeMember(this, name)
  }

  /**
   * Gets a namespace declaration or top-level whose exports contribute directly to this namespace.
   *
   * This includes containers that don't actually contain any `export` statements, but whose
   * exports would contribute to this namespace, if there were any.
   *
   * Does not include containers whose exports only contribute indirectly, through re-exports.
   * That is, there is at most one namespace associated with a given container.
   *
   * Namespaces defined by enum declarations have no exporting containers.
   */
  StmtContainer getAnExportingContainer() {
    getExportNamespace(result) = this
  }

  /**
   * Gets an access to this namespace from a type annotation.
   */
  NamespaceAccess getAnAccess() {
    this = NameResolution::getNamespaceFromAccess(result)
  }

  /**
   * Gets a definition of this namespace, that is, a namespace declaration or enum declaration.
   *
   * Module root namespaces have no definitions.
   */
  NamespaceDefinition getADefinition() {
    this = NameResolution::getNamespaceFromDefinition(result)
  }

  /**
   * Gets the outermost scope from which this namespace can be accessed by a qualified name (without using an `import`).
   *
   * This is typically the top-level of a module, but for locally declared namespaces, this is the container where the namespace is declared.
   *
   * As a special rule, the root scope of a module namespace is the top-level of that module,
   * even though there is no qualified name associated with the module itself.
   * This means all namespaces have a unique root container.
   */
  Scope getRootScope() {
    this = TNamespaceModuleRoot(result.getScopeElement())
    or
    exists (LocalNamespaceName local | this = TNamespaceLexicalRoot(local) | result = local.getScope())
    or
    result = getParent().getRootScope()
    or
    exists (ExternalModuleDeclaration decl | this = TExternalModule(decl.getName()) | result = decl.getScope())
  }

  /**
   * True if this is a namespace root, that is, it has no parent.
   *
   * Namespace roots are either top-level namespaces, or lexical namespaces that
   * contain the non-exported namespaces declared in a given scope.
   */
  predicate isRoot() {
    not exists (getParent())
  }

  /**
   * Holds if this is the export namespace of a module.
   */
  predicate isModuleRoot() {
    this instanceof TNamespaceModuleRoot or
    this instanceof TExternalModule
  }

  /**
   * Holds if this is the export namespace of the given module.
   */
  predicate isModuleRoot(StmtContainer mod) {
    this = TNamespaceModuleRoot(mod)
    or
    this = TExternalModule(getExternalModuleName(mod.(Module).getFile()))
    or
    this = TExternalModule(mod.(ExternalModuleDeclaration).getName())
  }

  /**
   * Gets the module defining this namespace, if any.
   */
  Module getModule() {
    result = getRootScope().getScopeElement().getTopLevel()
  }

  /**
   * Gets the qualified name by which this namespace can be accessed from its root container, or
   * the module name if this is the root namespace of a module.
   *
   * Note that the qualified name is not enough to uniquely identify a namespace at a global level,
   * as it does not generally include the namespace root.
   */
  string getQualifiedName() {
    exists (Module mod | this = TNamespaceModuleRoot(mod) and result = mod.getName())
    or
    exists (LocalNamespaceName local | this = TNamespaceLexicalRoot(local) | result = local.getName())
    or
    exists (Namespace parent, string name | this = TNamespaceMember(parent, name) |
      if parent.isModuleRoot()
      then result = name
      else result = parent.getQualifiedName() + "." + name)
    or
    this = TExternalModule(result)
  }

  /**
   * Gets a string with the name of the file that defines this namespace, with line
   * number information if the root container is not the top-level of the file.
   */
  string describeRoot() {
    result = describeRootScope(getRootScope())
  }

  /**
   * Gets a string constisting of the qualified name and a short description of the root container.
   */
  string toString() {
    if isModuleRoot()
    then result = describeRoot()
    else result = getQualifiedName() + " in " + describeRoot()
  }
}

/**
 * Describes the root of a namespace.
 */
private string describeRootScope(Scope scope) {
  if scope instanceof ModuleScope
  then exists (File file | file = scope.getScopeElement().(Module).getFile() |
    if file.getBaseName() = "index.d.ts"
    then result = "module " + file.getParentContainer().getBaseName()
    else result = file.getBaseName())

  else if scope instanceof ExternalModuleScope
  then result = "module " + scope.getScopeElement().(ExternalModuleDeclaration).getName()

  else if exists (scope.getScopeElement())
  then result = scope.getScopeElement().getLocation().toString()

  else result = "global scope"
}

/**
 * The canonical name of a type, underlying the `TypeName` definition.
 */
private newtype TTypeName =
  TExportedTypeName(Namespace namespace, string name) {
    exists (TypeDefinition def |
      isExportedStmt(def) and
      def.getName() = name and
      def.(Stmt).getContainer() = namespace.getAnExportingContainer())
    or
    exists (EnumMember member |
      namespace = NameResolution::getNamespaceFromDefinition(member.getDeclaringEnum()) and
      member.getName() = name)
  }
  or
  TLexicalTypeName(LocalTypeName local) {
    exists (TypeDefinition def |
      not isExportedStmt(def) and
      def.getIdentifier().(TypeDecl).getLocalTypeName() = local)
  }

/**
 * The canonical name of a type definition.
 *
 * Note that anonymous class expressions and type parameters do not have canonical names.
 */
class TypeName extends TTypeName {
  /**
   * Gets the unqualified name of this type.
   */
  string getName() {
    this = TExportedTypeName(_, result)
    or
    exists (LocalTypeName local | this = TLexicalTypeName(local) |
      result = local.getName())
  }

  /**
   * Gets the qualified name by which the type can be accessed from its root container.
   *
   * Note that the qualified name is not enough to uniquely identify a type at a global level,
   * as it does not generally include the namespace root.
   */
  string getQualifiedName() {
    exists (Namespace namespace, string name | this = TExportedTypeName(namespace, name) |
      if namespace.isModuleRoot()
      then result = name
      else result = namespace.getQualifiedName() + "." + name)
    or
    exists (LocalTypeName local | this = TLexicalTypeName(local) |
      result = local.getName())
  }

  /**
   * Gets the outermost scope from which this type can be accessed by a qualified name (without using an `import`).
   *
   * This is typically the top-level of a module, but for locally declared types (e.g. types declared inside a function),
   * this is the container where the type is declared.
   */
  Scope getRootScope() {
    exists (Namespace namespace | this = TExportedTypeName(namespace, _) |
      result = namespace.getRootScope())
    or
    exists (LocalTypeName local | this = TLexicalTypeName(local) |
      result = local.getScope())
  }

  /**
   * Gets a string constisting of the qualified name and a short description of the root container.
   */
  string toString() {
    result = getQualifiedName() + " in " + describeRootScope(getRootScope())
  }

  /**
   * Gets a definition of this type.
   *
   * Most types have a single definition, but interfaces may have multiple definitions.
   */
  TypeDefinition getADefinition() {
    result.getTypeName() = this
  }

  /**
   * Gets an access to this type.
   */
  TypeAccess getAnAcccess() {
    result.getTypeName() = this
  }
}

/**
 * Provides predicates for resolving syntactic names and definitions to their canonical names.
 *
 * This module should rarely be used directly. Instead, the results should be accessed through
 * class methods such as `TypeAccess.getTypeName`.
 */
module NameResolution {
  /**
   * Gets the namespace associated with the given module top-level or namespace declaration.
   */
  Namespace getNamespaceFromContainer(StmtContainer container) {
    result.getAnExportingContainer() = container
  }

  /**
   * Gets the namespace defined by the given namespace declaration or enum declaration.
   */
  Namespace getNamespaceFromDefinition(NamespaceDefinition def) {
    if hasReassignedExportTarget(def) then
      result = getReassignedExportTarget(def)
    else if isExportedStmt(def) then
      result = TNamespaceMember(getExportNamespace(def.getContainer()), def.getName())
    else
      result = TNamespaceLexicalRoot(def.getId().(LocalNamespaceDecl).getLocalNamespaceName())
  }

  /**
   * Gets the namespace being declared or aliased by the given declaration.
   */
  Namespace getNamespaceFromDeclarationId(LocalNamespaceDecl id) {
    // namespace A {...}  |  enum A {...}
    exists (NamespaceDefinition decl | decl.getId() = id | result = getNamespaceFromDefinition(decl))
    or
    // import {A} from 'lib'  |  import {B as A} from 'lib'  |  import A from 'lib'
    exists (ImportDeclaration decl, ImportSpecifier spec |
      id = spec.getLocal() and
      spec = decl.getASpecifier() and
      result = getNamespaceFromImport(decl).getNamespaceMember(spec.getImportedName()))
    or
    // import * as A from 'lib'
    exists (ImportDeclaration decl, ImportNamespaceSpecifier spec |
      id = spec.getLocal() and
      spec = decl.getASpecifier() and
      result = getNamespaceFromImport(decl))
    or
    // import A = B
    exists (ImportEqualsDeclaration decl |
      id = decl.getId() and
      result = getNamespaceFromExpr(decl.getImportedEntity()))
  }

  /**
   * Gets the namespace whose members are imported by the given declaration.
   */
  Namespace getNamespaceFromImport(ImportDeclaration decl) {
    result.isModuleRoot(decl.getImportedModule())
    or
    exists (ExternalModuleDeclaration extern |
      extern.getName() = decl.getImportedPath().getValue() and
      result = getNamespaceFromContainer(extern))
  }

  /**
   * Gets the namespace whose members are re-exported by the given declaration.
   */
  Namespace getNamespaceFromReExport(ReExportDeclaration decl) {
    result.isModuleRoot(decl.getImportedModule())
  }

  /**
   * Resolves a local namespace name to its global identifier.
   */
  Namespace getNamespaceFromLocalName(LocalNamespaceName local) {
    result = getNamespaceFromDeclarationId(local.getADeclaration())
  }

  /**
   * Gets the namespace referenced by the given access.
   */
  Namespace getNamespaceFromAccess(NamespaceAccess access) {
    exists (LocalNamespaceAccess local | local = access |
      result = getNamespaceFromLocalName(local.getLocalNamespaceName()))
    or
    exists (LocalNamespaceAccess local | local = access |
      not exists (local.getLocalNamespaceName()) and
      result = getNamespaceFromGlobal(local.getName()))
    or
    exists (QualifiedNamespaceAccess qualified | qualified = access |
      result = getNamespaceFromAccess(qualified.getQualifier()).getNamespaceMember(qualified.getIdentifier().getName()))
  }

  /**
   * Gets the namespace referenced by an exported expression.
   *
   * It is possible to export qualified names using:
   * ```
   * export default A.B.C
   * ```
   */
  Namespace getNamespaceFromExpr(Expr expr) {
    exists (ExportVarAccess access | access = expr |
      result = getNamespaceFromLocalName(access.getLocalNamespaceName()))
    or
    exists (PropAccess access | access = expr |
      result = getNamespaceFromExpr(access.getBase()).getNamespaceMember(access.getPropertyName()))
  }

  /**
   * Gets the globally declared namespace of the given name, provided that this is declared in a `d.ts` file.
   */
  Namespace getNamespaceFromGlobal(string name) {
    exists (NamespaceDefinition def |
      def.getName() = name and
      def.(Stmt).getContainer() = getAnAmbientGlobalContainer() and
      not isExportedStmt(def) and
      result = getNamespaceFromDefinition(def))
    or
    exists (ExportAsNamespaceDeclaration exprt |
      name = exprt.getIdentifier().getName() and
      result.isModuleRoot(exprt.getTopLevel()))
  }

  /**
   * Gets a member of `namespace` that is not a child of that namespace.
   *
   * This happens when a module exports a namespace originating from elsewhere.
   * For example:
   * ```
   * // lib.js
   * export namespace A {}
   *
   * // foo.js
   * export {A} from './lib'
   * ```
   * The namespaces of these two modules both have a member `A` referring to the same namespace.
   * `A` is a child of the `lib.js` namespace, whereas it is an an *aliased member* of the `foo.js` namespace.
   */
  Namespace getAliasedNamespaceMember(Namespace namespace, string name) {
    exists (ExportDeclaration decl, LocalNamespaceName exportedName | namespace.isModuleRoot(decl.getEnclosingModule()) |
      decl.exportsAs(exportedName, name) and
      result = getNamespaceFromLocalName(exportedName))
    or
    // export default A  |  export default A.B.C
    exists (ExportDefaultDeclaration decl |
      namespace.isModuleRoot(decl.getEnclosingModule()) and
      name = "default" and
      result = getNamespaceFromExpr(decl.getOperand()))
  }

  /**
   * Gets the canonical name of the type being defined by the given definition.
   */
  TypeName getTypeNameFromDefinition(TypeDefinition def) {
    if isExportedStmt(def)
    then result = TExportedTypeName(getNamespaceFromContainer(def.(Stmt).getContainer()), def.getName())
    else if def instanceof EnumMember
    then result = TExportedTypeName(getNamespaceFromDefinition(def.(EnumMember).getDeclaringEnum()), def.getName())
    else result = TLexicalTypeName(def.getIdentifier().(TypeDecl).getLocalTypeName())
  }

  /**
   * Gets the canonical name of the type being declared or imported by the given identifier.
   */
  TypeName getTypeNameFromDeclarationId(TypeDecl id) {
    exists (TypeDefinition def | def.getIdentifier() = id | result = getTypeNameFromDefinition(def))
    or
    exists (ImportDeclaration decl, ImportSpecifier spec |
      id = spec.getLocal() and
      spec = decl.getASpecifier() and
      result = getNamespaceFromImport(decl).getTypeMember(spec.getImportedName()))
    or
    exists (ImportEqualsDeclaration decl |
      id = decl.getId() and
      result = getTypeNameFromExpr(decl.getImportedEntity()))
  }

  /**
   * Gets the canonical name of the type referred to by a local type name.
   */
  TypeName getTypeNameFromLocalName(LocalTypeName name) {
    result = getTypeNameFromDeclarationId(name.getADeclaration())
  }

  /**
   * Gets the canonical name of the type being accessed.
   */
  TypeName getTypeNameFromAccess(TypeAccess access) {
    exists (LocalTypeAccess local | local = access |
      result = getTypeNameFromLocalName(local.getLocalTypeName()))
    or
    exists (LocalTypeAccess local | local = access |
      not exists (local.getLocalTypeName()) and
      result = getTypeNameFromGlobal(local.getName()))
    or
    exists (QualifiedTypeAccess qualified | qualified = access |
      result = getNamespaceFromAccess(qualified.getQualifier()).getTypeMember(qualified.getIdentifier().getName()))
  }

  /**
   * Gets the type name referenced by an expression, which can be an exported and imported expression.
   */
  TypeName getTypeNameFromExpr(Expr expr) {
    exists (ExportVarAccess access | access = expr |
      result = getTypeNameFromLocalName(access.getLocalTypeName()))
    or
    exists (PropAccess access | access = expr |
      result = getNamespaceFromExpr(access.getBase()).getTypeMember(access.getPropertyName()))
  }

  /**
   * Gets the globally declared type of the given name, provided that this is declared in a `d.ts` file.
   */
  TypeName getTypeNameFromGlobal(string name) {
    exists (TypeDefinition def |
      def.getName() = name and
      def.(Stmt).getContainer() = getAnAmbientGlobalContainer() and
      not isExportedStmt(def) and
      result = getTypeNameFromDefinition(def))
  }

  /**
   * Gets a type member of `namespace` that is not a child of that namespace.
   *
   * See `getAliasedNamespaceMember` for more details.
   */
  TypeName getAliasedTypeMember(Namespace namespace, string name) {
    exists (ExportDeclaration decl, LocalTypeName exportedName | namespace.isModuleRoot(decl.getEnclosingModule()) |
      decl.exportsAs(exportedName, name) and
      result = getTypeNameFromLocalName(exportedName))
    or
    // export default A  |  export default A.B.C
    exists (ExportDefaultDeclaration decl |
      namespace.isModuleRoot(decl.getEnclosingModule()) and
      name = "default" and
      result = getTypeNameFromExpr(decl.getOperand()))
  }

  /**
   * Gets a statement that contributes ambient types and namespaces which should be available globally.
   */
  StmtContainer getAnAmbientGlobalContainer() {
    result instanceof TopLevel and
    not result instanceof Module and
    result.getFile().getBaseName().matches("%.d.ts") and
    exists (ReferenceImport im | result = im.getImportedTopLevel())
    or
    result instanceof GlobalAugmentationDeclaration and
    result.getFile().getBaseName() = "index.d.ts"
    or
    result.(TopLevel).getFile().getBaseName() = "lib.d.ts"
  }

  /**
   * For internal use.
   *
   * A symbol from the TypeScript compiler, used for name binding.
   *
   * Symbols correspond to qualified names, represented as a prefix tree.
   * That is, the parent of a symbol is the symbol corresponding to its prefix.
   *
   * There is not a unique symbol per qualified name. That is, there can be
   * several symbols representing the name `foo.bar`, each one relative to
   * a different scope.
   *
   * The database contains bindings between symbols, types, and AST nodes.
   */
  class Symbol extends @symbol {
    /**
     * Gets the parent of this symbol, i.e. the prefix of its qualified name.
     */
    Symbol getParent() { symbol_parent(this, result) }

    /**
     * Gets a child of this symbol, i.e. an extension of its qualified name.
     */
    Symbol getAChild() { result.getParent() = this }

    /**
     * Gets the name of this symbol without prefix.
     */
    string getName() { symbols(this, _, result) }

    /**
     * Gets the name of an external module represented by this symbol, if any.
     */
    string getExternalModuleName() {
      symbol_module(this, result)
    }

    /**
     * Gets the name of a global variable aliasing this symbol though an `export as X` declaration.
     */
    string getGlobalName() {
      symbol_global(this, result)
    }

    /**
     * Gets the module definition corresponding to this symbol, if any.
     */
    Module getModule() {
      ast_node_symbol(result, this)
    }

    /**
     * Gets a type refers to this symbol.
     */
    TypeReference getATypeReference() {
      type_symbol(result, this)
    }

    /**
     * Gets a type definition referred to by this symbol.
     */
    TypeDefinition getATypeDefinition() {
      ast_node_symbol(result, this)
    }

    /**
     * Holds if this symbol has a child, i.e. an extension of its qualified name.
     */
    predicate hasChild() {
      exists (getAChild())
    }

    /**
     * Holds if there exists a type that refers to this symbol.
     */
    predicate hasTypeReference() {
      exists (getATypeReference())
    }

    /** Holds if this symbol is exported by its parent. */
    predicate isExportedMember() {
      this instanceof @member_symbol
    }

    /** Holds if this is the given qualified name, rooted in the global scope. */
    predicate hasQualifiedName(string globalName) {
      globalName = getGlobalName()
      or
      exists (string prefix |
        getParent().hasQualifiedName(prefix) and
        globalName = prefix + "." + getName())
    }

    /** Holds if this is the given qualified name, rooted in the given external module. */
    predicate hasQualifiedName(string moduleName, string exportedName) {
      moduleName = getParent().getExternalModuleName() and
      exportedName = getName()
      or
      exists (string prefix |
        getParent().hasQualifiedName(moduleName, prefix) and
        exportedName = prefix + "." + getName())
    }

    string toString() { result = getName() }
  }
}
