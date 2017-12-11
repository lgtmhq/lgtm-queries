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
}

/**
 * The canonical name of a namespace, underlying the `Namespace` type.
 */
private newtype TNamespace =
  /** The root namespace of a module, containing its exported members. */
  TNamespaceModuleRoot(Module mod)
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

/** Gets the namespace to which `export` statements in the given container should contribute. */
private TNamespace getExportNamespace(StmtContainer container) {
  exists (Module mod | container = mod |
    result = TNamespaceModuleRoot(mod))
  or
  exists (NamespaceDeclaration decl | container = decl |
    if isExportedStmt(decl)
    then result = TNamespaceMember(getExportNamespace(decl.getEnclosingContainer()), decl.getName())
    else result = TNamespaceLexicalRoot(decl.getLocalNamespaceName()))
}

/**
 * The canonical name of a namespace, representing a module or TypeScript namespace declaration.
 */
class Namespace extends TNamespace {
  /** Gets the unqualified name of this namespace, or the the file name it is the root namespace of a module. */
  string getName() {
    exists (Module mod | this = TNamespaceModuleRoot(mod) | result = describeRootContainer(mod))
    or
    exists (LocalNamespaceName local | this = TNamespaceLexicalRoot(local) | result = local.getName())
    or
    this = TNamespaceMember(_, result)
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
   * Gets the outermost scope from which the namespace can be accessed by a qualified name (without using an `import`).
   *
   * This is typically the top-level of a module, but for locally declared namespaces, this is the container where the namespace is declared.
   *
   * As a special rule, the root container of a module namespace is the top-level of that module,
   * even though there is no qualified name associated with the module itself.
   * This means all namespaces have a unique root container.
   */
  StmtContainer getRootContainer() {
    this = TNamespaceModuleRoot(result)
    or
    exists (LocalNamespaceName local | this = TNamespaceLexicalRoot(local) | result = local.getScope().getScopeElement())
    or
    result = getParent().getRootContainer()
  }

  /**
   * Gets the top-level in which this namespace is defined.
   */
  TopLevel getTopLevel() {
    result = getRootContainer().getTopLevel()
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
    this instanceof TNamespaceModuleRoot
  }

  /**
   * Holds if this is the export namespace of the given module.
   */
  predicate isModuleRoot(Module mod) {
    this = TNamespaceModuleRoot(mod)
  }

  /**
   * Gets the module defining this namespace, if any.
   */
  Module getModule() {
    result = getTopLevel()
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
  }

  /**
   * Gets a string with the name of the file that defines this namespace, with line
   * number information if the root container is not the top-level of the file.
   */
  string describeRoot() {
    result = describeRootContainer(getRootContainer())
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
private string describeRootContainer(StmtContainer container) {
  if container instanceof Module
  then result = container.getFile().getBaseName()
  else result = container.getLocation().toString()
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
  StmtContainer getRootContainer() {
    exists (Namespace namespace | this = TExportedTypeName(namespace, _) |
      result = namespace.getRootContainer())
    or
    exists (LocalTypeName local | this = TLexicalTypeName(local) |
      result = local.getScope().getScopeElement())
  }

  /**
   * Gets a string constisting of the qualified name and a short description of the root container.
   */
  string toString() {
    result = getQualifiedName() + " in " + describeRootContainer(getRootContainer())
  }

  /**
   * Gets a definition of this type.
   *
   * Most types have a single definition, but interfaces may have multiple definitions.
   */
  TypeDefinition getADefinition() {
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
    if isExportedStmt(def)
    then result = TNamespaceMember(getExportNamespace(def.getContainer()), def.getName())
    else result = TNamespaceLexicalRoot(def.getId().(LocalNamespaceDecl).getLocalNamespaceName())
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
  }

  /**
   * Gets the namespace whose members are imported by the given declaration.
   */
  Namespace getNamespaceFromImport(ImportDeclaration decl) {
    result.isModuleRoot(decl.getImportedModule())
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
  Namespace getNamespaceFromExportExpr(Expr expr) {
    exists (ExportVarAccess access | access = expr |
      result = getNamespaceFromLocalName(access.getLocalNamespaceName()))
    or
    exists (PropAccess access | access = expr |
      result = getNamespaceFromExportExpr(access.getBase()).getNamespaceMember(access.getPropertyName()))
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
      result = getNamespaceFromExportExpr(decl.getOperand()))
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
    exists (QualifiedTypeAccess qualified | qualified = access |
      result = getNamespaceFromAccess(qualified.getQualifier()).getTypeMember(qualified.getIdentifier().getName()))
  }

  /**
   * Gets the type name referenced by an exported expression.
   *
   * Unlike namespaces, these cannot be qualified names.
   */
  TypeName getTypeNameFromExportExpr(Expr expr) {
    exists (ExportVarAccess access | access = expr |
      result = getTypeNameFromLocalName(access.getLocalTypeName()))
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
      result = getTypeNameFromExportExpr(decl.getOperand()))
  }
}

