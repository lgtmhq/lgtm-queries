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

import javascript

/**
 * A statement that defines a namespace, that is, a namespace declaration or enum declaration.
 *
 * Declarations that declare an alias for a namespace (i.e. an import) are not
 * considered to be namespace definitions.
 */
class NamespaceDefinition extends Stmt, @namespacedefinition, AST::ValueNode {
  /**
   * Gets the identifier naming the namespace.
   */
  Identifier getId() {
    result = this.(NamespaceDeclaration).getId()
    or
    result = this.(EnumDeclaration).getIdentifier()
  }

  /**
   * Gets unqualified name of the namespace being defined.
   */
  string getName() {
    result = this.(NamespaceDeclaration).getName()
    or
    result = this.(EnumDeclaration).getName()
  }

  /**
   * Gets the local namespace name induced by this namespace.
   */
  LocalNamespaceName getLocalNamespaceName() {
    result = getId().(LocalNamespaceDecl).getLocalNamespaceName()
  }

  /**
   * Gets the canonical name of the namespace being defined.
   */
  Namespace getNamespace() {
    result = NameResolution::getNamespaceFromDefinition(this)
  }
}

/**
 * A TypeScript namespace declaration.
 *
 * This is also known as an "internal module" and can be declared
 * using the `module` or `namespace` keyword. For example:
 * ```
 * namespace util { ... }
 * module util { ... } // equivalent
 * ```
 *
 * Note that modules whose name is a string literal, called "external modules",
 * and are not namespace declarations.
 * For example, `declare module "X" {...}` is an external module declaration.
 * These are represented by `ExternalModuleDeclaration`.
 */
class NamespaceDeclaration extends NamespaceDefinition, StmtContainer, @namespacedeclaration {
  /** Gets the name of this namespace. */
  Identifier getId() {
    result = getChild(-1)
  }

  /** Gets the name of this namespace as a string. */
  string getName() {
    result = getId().getName()
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

  override ControlFlowNode getFirstControlFlowNode() {
    if hasDeclareKeyword(this) then
      result = this
    else
      result = getId()
  }
}

/**
 * A statement that defines a named type, that is, a class, interface, type alias, or enum declaration.
 *
 * Note that imports and type parameters are not type definitions.  Consider using `TypeDecl` to capture
 * a wider class of type declarations.
 */
class TypeDefinition extends ASTNode, @typedefinition {
  /**
   * Gets the identifier naming the type.
   */
  Identifier getIdentifier() {
    result = this.(ClassDefinition).getIdentifier() or
    result = this.(InterfaceDeclaration).getIdentifier() or
    result = this.(TypeAliasDeclaration).getIdentifier() or
    result = this.(EnumDeclaration).getIdentifier() or
    result = this.(EnumMember).getIdentifier()
  }

  /**
   * Gets the unqualified name of the type being defined.
   */
  string getName() {
    result = getIdentifier().getName()
  }

  /**
   * Gets the canonical name of the type being defined.
   */
  TypeName getTypeName() {
    result = NameResolution::getTypeNameFromDefinition(this)
  }

  /**
   * Gets the type defined by this declaration.
   */
  Type getType() {
    ast_node_type(getIdentifier(), result)
  }
}

/**
 * A TypeScript declaration of form `declare module "X" {...}` where `X`
 * is the name of an external module.
 */
class ExternalModuleDeclaration extends Stmt, StmtContainer, @externalmoduledeclaration {
  /**
   * Gets the string literal denoting the module name, such as `"fs"` in:
   * ```
   * declare module "fs" {...}
   * ```
   */
  StringLiteral getNameLiteral() {
    result = getChildExpr(-1)
  }

  /**
   * Gets the module name, such as `fs` in:
   * ```
   * declare module "fs" {...}
   * ```
   */
  string getName() {
    result = getNameLiteral().getStringValue()
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

  override predicate isAmbient() { any() }
}

/**
 * A TypeScript declaration of form `declare global {...}`.
 */
class GlobalAugmentationDeclaration extends Stmt, StmtContainer, @globalaugmentationdeclaration {
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

  override predicate isAmbient() { any() }
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

/**
 * A `require()` call in a TypeScript import-equals declaration, such as `require("foo")` in:
 * ```
 * import foo = require("foo");
 * ```
 *
 * These are special in that they may only occur in an import-equals declaration,
 * and the compiled output depends on the `--module` flag passed to the
 * TypeScript compiler.
 */
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
private class LiteralExternalModulePath extends PathExprInModule, ConstantString {
  LiteralExternalModulePath() {
    exists (ExternalModuleReference emr | this.getParentExpr*() = emr.getExpression())
  }

  override string getValue() { result = this.(ConstantString).getStringValue() }
}

/** A TypeScript "export-assign" declaration. */
class ExportAssignDeclaration extends Stmt, @exportassigndeclaration {
  /** Gets the expression exported by this declaration. */
  Expr getExpression() {
    result = getChild(0)
  }
}

/** A TypeScript export of form `export as namespace X` where `X` is an identifier. */
class ExportAsNamespaceDeclaration extends Stmt, @exportasnamespacedeclaration {
  /**
   * Gets the `X` in `export as namespace X`.
   */
  Identifier getIdentifier() {
    result = getChildExpr(0)
  }

  override predicate isAmbient() { any() }
}

/**
 * A type alias declaration, that is, a statement of form `type A = T`.
 */
class TypeAliasDeclaration extends @typealiasdeclaration, TypeParameterized, Stmt {
  /** Gets the name of this type alias as a string. */
  string getName() {
    result = getIdentifier().getName()
  }

  Identifier getIdentifier() {
    result = getChildTypeExpr(0)
  }

  override TypeParameter getTypeParameter(int n) {
    result = getChildTypeExpr(n + 2)
  }

  /**
   * Gets the `T` in `type A = T`.
   */
  TypeExpr getDefinition() {
    result = getChildTypeExpr(1)
  }

  override string describe() {
    result = "type alias " + getName()
  }

  override predicate isAmbient() {
    any()
  }

  /**
   * Gets the canonical name of the type being defined.
   */
  TypeName getTypeName() {
    result = NameResolution::getTypeNameFromDefinition(this)
  }
}

/**
 * A TypeScript interface declaration, inline interface type, or function type.
 */
class InterfaceDefinition extends @interfacedefinition, ClassOrInterface {
  override predicate isAbstract() {
    any()
  }
}

/** A TypeScript interface declaration. */
class InterfaceDeclaration extends Stmt, InterfaceDefinition, @interfacedeclaration {
  override Identifier getIdentifier() {
    result = getChild(0)
  }

  override TypeParameter getTypeParameter(int n) {
    exists (int astIndex | typeexprs(result, _, this, astIndex, _) | astIndex <= -2 and astIndex % 2 = 0 and n = -(astIndex + 2) / 2)
  }

  override StmtContainer getContainer() {
    result = Stmt.super.getContainer()
  }

  override predicate isAmbient() {
    any()
  }

  override string describe() {
    result = "interface " + getName()
  }

  /**
   * Gets the `n`th type from the `extends` clause of this interface, starting at 0.
   */
  override TypeExpr getSuperInterface(int n) {
    exists (int astIndex | typeexprs(result, _, this, astIndex, _) | astIndex <= -1 and astIndex % 2 = -1 and n = -(astIndex + 1) / 2)
  }

  /**
   * Gets any type from the `extends` clause of this interface.
   */
  override TypeExpr getASuperInterface() {
    result = InterfaceDefinition.super.getASuperInterface()
  }
}

/** An inline TypeScript interface type, such as `{x: number; y: number}`. */
class InterfaceTypeExpr extends TypeExpr, InterfaceDefinition, @interfacetypeexpr {
  override Identifier getIdentifier() { none() }

  override StmtContainer getContainer() {
    result = TypeExpr.super.getContainer()
  }

  override string describe() {
    result = "anonymous interface"
  }
}

/**
 * A TypeScript function type, such as `(x: string) => number` or a
 * constructor type such as `new (x: string) => Object`.
 */
class FunctionTypeExpr extends TypeExpr, @functiontypeexpr {
  /** Holds if this is a constructor type, such as `new (x: string) => Object`. */
  predicate isConstructor() { this instanceof ConstructorTypeExpr }

  /** Gets the function AST node that holds the parameters and return type. */
  FunctionExpr getFunction() { result = getChildExpr(0) }

  /** Gets the `n`th parameter of this function type. */
  Parameter getParameter(int n) { result = getFunction().getParameter(n) }

  /** Gets any of the parameters of this function type. */
  Parameter getAParameter() { result = getFunction().getAParameter() }

  /** Gets the number of parameters of this function type. */
  int getNumParameter() { result = getFunction().getNumParameter() }

  /** Gets the `n`th type parameter of this function type. */
  TypeParameter getTypeParameter(int n) { result = getFunction().getTypeParameter(n) }

  /** Gets any of the type parameters of this function type. */
  TypeParameter getATypeParameter() { result = getFunction().getATypeParameter() }

  /** Gets the number of type parameters of this function type. */
  int getNumTypeParameter() { result = getFunction().getNumTypeParameter() }

  /** Gets the return type of this function type, if any. */
  TypeExpr getReturnTypeAnnotation() { result = getFunction().getReturnTypeAnnotation() }
}

/** A constructor type, such as `new (x: string) => Object`. */
class ConstructorTypeExpr extends FunctionTypeExpr, @constructortypeexpr {}

/** A function type that is not a constructor type, such as `(x: string) => number`. */
class PlainFunctionTypeExpr extends FunctionTypeExpr, @plainfunctiontypeexpr {}

/** A possibly qualified identifier that declares or refers to a type. */
abstract class TypeRef extends ASTNode {
}

/** An identifier declaring a type name, that is, the name of a class, interface, type parameter, or import. */
class TypeDecl extends Identifier, TypeRef, LexicalDecl {
  TypeDecl() {
    this = any(ClassOrInterface ci).getIdentifier() or
    this = any(TypeParameter tp).getIdentifier() or
    this = any(ImportSpecifier im | not im instanceof ImportNamespaceSpecifier).getLocal() or
    this = any(ImportEqualsDeclaration im).getId() or
    this = any(TypeAliasDeclaration td).getIdentifier() or
    this = any(EnumDeclaration ed).getIdentifier() or
    this = any(EnumMember member).getIdentifier()
  }

  /**
   * Gets the local type name being declared.
   *
   * If this is an import or type alias, the local type name represents the local alias.
   */
  LocalTypeName getLocalTypeName() {
    result.getADeclaration() = this
  }

  /**
   * Gets a string describing the type being declared, consisting of the declaration kind and
   * the name being declared, such as `class C` for a class declaration `C`.
   */
  string describe() {
    exists (ClassOrInterface ci | this = ci.getIdentifier() | result = ci.describe()) or
    exists (TypeParameter tp | this = tp.getIdentifier() | result = "type parameter " + getName()) or
    exists (TypeAliasDeclaration td | this = td.getIdentifier() | result = "type alias " + getName()) or
    exists (EnumDeclaration enum | this = enum.getIdentifier() | result = "enum " + getName()) or
    exists (EnumMember member | this = member.getIdentifier() | result = "enum member " + member.getPrefixedName()) or
    exists (ImportSpecifier im | this = im.getLocal() | result = "imported type " + getName())
  }
}

/**
 * The local name for a type in a particular scope.
 *
 * It is possible for two distinct local type names to refer to the same underlying
 * type through imports or type aliases. For example:
 * ```
 * namespace A {
 *   export class C {}
 * }
 * namespace B {
 *   import C = A.C;
 * }
 * ```
 * In the above example, two distinct local type names exist for the type `C`:
 * one in `A` and one in `B`.
 * Since a local type name is always specific to one scope, it is not possible
 * for the two namespaces to share a single local type name for `C`.
 *
 * There may be multiple declarations of a given local type name, for example:
 * ```
 * interface Point { x: number; }
 * interface Point { y: number; }
 * ```
 * In the above example, the two declarations of `Point` refer to the same
 * local type name.
 */
class LocalTypeName extends @local_type_name, LexicalName {
  /** Gets the local name of this type. */
  string getName() {
    local_type_names(this, result, _)
  }

  /** Gets the scope this type name is declared in. */
  Scope getScope() {
    local_type_names(this, _, result)
  }

  /** Gets a textual representation of this element. */
  string toString() {
    result = getName()
  }

  /**
   * Gets a declaration of this type name.
   *
   * All local type names have at least one declaration and may have
   * multiple declarations in case these are interface declarations.
   */
  TypeDecl getADeclaration() {
    typedecl(result, this)
  }

  /**
   * Gets the first declaration of this type name.
   */
  TypeDecl getFirstDeclaration() {
    result = min(getADeclaration() as decl order by decl.getFirstToken().getIndex())
  }

  /** Gets a use of this type name in a type annotation. */
  LocalTypeAccess getATypeAccess() {
    typebind(result, this)
  }

  /** Gets a use of this type name in an export. */
  ExportVarAccess getAnExportAccess() {
    typebind(result, this)
  }

  /** Gets an identifier that refers to this type name. */
  Identifier getAnAccess() {
    typebind(result, this)
  }

  override DeclarationSpace getDeclarationSpace() {
    result = "type"
  }
}

/**
 * The local name for a namespace in a particular scope.
 *
 * Namespace declarations and imports can give rise to local namespace names.
 * For example, the following declarations declare two local namespace names,
 * `A` and `B`:
 * ```
 * import A from './A';
 * namespace B {}
 * ```
 *
 * It is possible for a namespace to have multiple aliases; each alias corresponds
 * to a distinct local namespace name. For example, there are three distinct local
 * namespace names for `A` in this example:
 * ```
 * namespace A {}
 * namespace Q {
 *   import B = A;
 *   import C = A;
 * }
 * ```
 * There is one local namespace name for the declaration of `A` and one for each import.
 */
class LocalNamespaceName extends @local_namespace_name, LexicalName {
  /** Gets the local name of this namespace. */
  string getName() {
    local_namespace_names(this, result, _)
  }

  /** Gets the scope this namespace name is declared in. */
  Scope getScope() {
    local_namespace_names(this, _, result)
  }

  /** Gets a textual representation of this element. */
  string toString() {
    result = getName()
  }

  /**
   * Gets a declaration of this namespace name.
   *
   * All local namespace names have at least one declaration and may have
   * multiple declarations unless it comes from an import.
   */
  LocalNamespaceDecl getADeclaration() {
    namespacedecl(result, this)
  }

  /**
   * Gets the first declaration of this namespace name.
   */
  LocalNamespaceDecl getFirstDeclaration() {
    result = min(getADeclaration() as decl order by decl.getFirstToken().getIndex())
  }

  /** Gets a use of this namespace name in a type annotation. */
  LocalNamespaceAccess getATypeAccess() {
    namespacebind(result, this)
  }

  /** Gets a use of this namespace in an export. */
  ExportVarAccess getAnExportAccess() {
    namespacebind(result, this)
  }

  /** Gets an identifier that refers to this namespace name. */
  Identifier getAnAccess() {
    namespacebind(result, this)
  }

  /**
   * Gets the canonical name of the namespace referenced by this name.
   */
  Namespace getNamespace() {
    result = NameResolution::getNamespaceFromLocalName(this)
  }

  override DeclarationSpace getDeclarationSpace() {
    result = "namespace"
  }
}

/**
 * A type expression, that is, an AST node that is part of a TypeScript type annotation.
 *
 * This class includes only explicit type annotations -
 * types inferred by the TypeScript compiler are not type expressions.
 */
class TypeExpr extends ExprOrType, @typeexpr {
  string toString() {
    typeexprs(this, _, _, _, result)
  }

  /** Holds if this is the `any` type. */
  predicate isAny() { none() }

  /** Holds if this is the `string` type. Does not hold for the (rarely used) `String` type. */
  predicate isString() { none() }

  /** Holds if this is the `string` or `String` type. */
  predicate isStringy() { none() }

  /** Holds if this is the `number` type. Does not hold for the (rarely used) `Number` type. */
  predicate isNumber() { none() }

  /** Holds if this is the `number` or `Number`s type. */
  predicate isNumbery() { none() }

  /** Holds if this is the `boolean` type. Does not hold for the (rarely used) `Boolean` type. */
  predicate isBoolean() { none() }

  /** Holds if this is the `boolean` or `Boolean` type. */
  predicate isBooleany() { none() }

  /** Holds if this is the `undefined` type. */
  predicate isUndefined() { none() }

  /** Holds if this is the `null` type. */
  predicate isNull() { none() }

  /** Holds if this is the `void` type. */
  predicate isVoid() { none() }

  /** Holds if this is the `never` type. */
  predicate isNever() { none() }

  /** Holds if this is the `this` type. */
  predicate isThis() { none() }

  /** Holds if this is the `symbol` type. */
  predicate isSymbol() { none() }

  /** Holds if this is the `unique symbol` type. */
  predicate isUniqueSymbol() { none() }

  /** Holds if this is the `Function` type. */
  predicate isRawFunction() { none() }

  /** Holds if this is the `object` type. */
  predicate isObjectKeyword() { none() }

  /** Gets this type expression, with any surrounding parentheses removed. */
  TypeExpr stripParens() {
    result = this
  }

  override predicate isAmbient() { any() }

  /**
   * Gets the static type expressed by this type annotation.
   *
   * Has no result if this occurs in a TypeScript file that was extracted
   * without type information.
   */
  Type getType() {
    ast_node_type(this, result)
  }
}

/**
 * Classes that are internally represented as a keyword type.
 */
private class KeywordTypeExpr extends @keywordtypeexpr, TypeExpr {
  string getName() { literals(result, _, this) }

  override predicate isAny() { getName() = "any" }
  override predicate isString() { getName() = "string" }
  override predicate isStringy() { getName() = "string" }
  override predicate isNumber() { getName() = "number" }
  override predicate isNumbery() { getName() = "number" }
  override predicate isBoolean() { getName() = "boolean" }
  override predicate isBooleany() { getName() = "boolean" }
  override predicate isUndefined() { getName() = "undefined" }
  override predicate isNull() { getName() = "null" }
  override predicate isVoid() { getName() = "void" }
  override predicate isNever() { getName() = "never" }
  override predicate isThis() { getName() = "this" }
  override predicate isSymbol() { getName() = "symbol" }
  override predicate isUniqueSymbol() { getName() = "unique symbol" }
  override predicate isObjectKeyword() { getName() = "object" }
}

/**
 * A use of the predefined type `any`, `string`, `number`, `boolean`, `null`, `undefined`, `void`, `never`, `symbol`, or `object`.
 */
class PredefinedTypeExpr extends KeywordTypeExpr {
  PredefinedTypeExpr() {
    not isThis() // The only keyword type that we don't consider a "predefined" type
  }
}

/**
 * A use of the `this` type.
 */
class ThisTypeExpr extends KeywordTypeExpr {
  ThisTypeExpr() {
    isThis()
  }
}

/**
 * A possibly qualified name that is used as part of a type, such as `Date` or `http.ServerRequest`.
 *
 * Type arguments are not part of a type access but there are convenience methods in this class
 * for accessing them.
 */
class TypeAccess extends @typeaccess, TypeExpr, TypeRef {
  /** Gets the identifier naming the type without any qualifier, such as `ServerRequest` in `http.ServerRequest`. */
  Identifier getIdentifier() { none() }

  /**
   * Gets the enclosing generic type expression providing type arguments to this type, if any.
   *
   * For example, in `Array<number>`, the `Array` part is a type access with `Array<number>`
   * being its enclosing generic type.
   */
  GenericTypeExpr getAsGenericType() { result.getTypeAccess() = this }

  /**
   * Holds if there are type arguments provided to this type by an enclosing generic type expression.
   *
   * For example, in `Array<number>`, the `Array` part is a type access having type arguments.
   */
  predicate hasTypeArguments() { exists(getAsGenericType()) }

  /**
   * Gets the `n`th type argument provided to this type by the enclosing generic type expression, if any.
   *
   * For example, in `Array<number>`, the `Array` part is a type access having the type argument `number`.
   */
  TypeExpr getTypeArgument(int n) { result = getAsGenericType().getTypeArgument(n) }

  /**
   * Gets a type argument provided to this type by the enclosing generic type expression, if any.
   *
   * For example, in `Array<number>`, the `Array` part is a type access having the type argument `number`.
   */
  TypeExpr getATypeArgument() { result = getAsGenericType().getATypeArgument() }

  /**
   * Gets the number of type arguments provided to this type by the enclosing generic type expression,
   * if any, or 0 otherwise.
   *
   * For example, in `Array<number>`, the `Array` part is a type access having 1 type argument.
   */
  int getNumTypeArgument() {
    if exists(getAsGenericType())
    then result = getAsGenericType().getNumTypeArgument()
    else result = 0
  }

  /**
   * Gets the canonical name of the type being accessed.
   */
  TypeName getTypeName() {
    result = NameResolution::getTypeNameFromAccess(this)
  }
}

/** An identifier that is used as part of a type, such as `Date`. */
class LocalTypeAccess extends @localtypeaccess, TypeAccess, Identifier, LexicalAccess {
  override predicate isStringy() { getName() = "String" }
  override predicate isNumbery() { getName() = "Number" }
  override predicate isBooleany() { getName() = "Boolean" }
  override predicate isRawFunction() { getName() = "Function" }

  override Identifier getIdentifier() { result = this }

  /**
   * Gets the local type name being referenced by this identifier, if any.
   *
   * Names that refer to a declaration in an external `d.ts` file, such as in
   * the built-in `lib.d.ts` prelude, do not have a local typename.
   *
   * For example, in `Array<number>`, the `Array` name will usually not have
   * a local type name as it is declared in `lib.d.ts`.
   */
  LocalTypeName getLocalTypeName() {
    result.getAnAccess() = this
  }
}

/**
 * A qualified name that is used as part of a type, such as `http.ServerRequest`.
 */
class QualifiedTypeAccess extends @qualifiedtypeaccess, TypeAccess {
  /**
   * Gets the qualifier in front of the name, such as `http` in `http.ServerRequest`.
   *
   * If the prefix consists of multiple identifiers, the qualifier is itself a qualified namespace access.
   * For example, the qualifier of `lib.util.List` is `lib.util`.
   */
  NamespaceAccess getQualifier() { result = getChildTypeExpr(0) }

  /** Gets the last identifier in the name, such as `ServerRequest` in `http.ServerRequest`. */
  override Identifier getIdentifier() { result = getChildTypeExpr(1) }
}

/**
 * A type consisting of a name and at least one type argument, such as `Array<number>`.
 *
 * For convenience, the methods for accessing type arguments are also made available
 * on the `TypeAccess` class.
 */
class GenericTypeExpr extends @generictypeexpr, TypeExpr {
  /** Gets the name of the type, such as `Array` in `Array<number>`. */
  TypeAccess getTypeAccess() { result = getChildTypeExpr(-1) }

  /** Gets the `n`th type argument, starting at 0. */
  TypeExpr getTypeArgument(int n) { result = getChildTypeExpr(n) and n >= 0 }

  /** Gets any of the type arguments. */
  TypeExpr getATypeArgument() { result = getTypeArgument(_) }

  /** Gets the number of type arguments. This is always at least one. */
  int getNumTypeArgument() { result = count(getATypeArgument()) }
}

/**
 * A string, number, or boolean literal used as a type.
 *
 * Note that the `null` and `undefined` types are considered predefined types, not literal types.
 */
class LiteralTypeExpr extends @literaltypeexpr, TypeExpr {
  /** Gets the value of this literal, as a string. */
  string getValue() {
    literals(result, _, this)
  }

  /**
   * Gets the raw source text of this literal, including quotes for
   * string literals.
   */
  string getRawValue() {
    literals(_, result, this)
  }
}

/** A string literal used as a type. */
class StringLiteralTypeExpr extends @stringliteraltypeexpr, LiteralTypeExpr {
}

/** A number literal used as a type. */
class NumberLiteralTypeExpr extends @numberliteraltypeexpr, LiteralTypeExpr {
  /** Gets the integer value of this literal type. */
  int getIntValue() {
    result = getValue().toInt()
  }
}

/** A boolean literal used as a type. */
class BooleanLiteralTypeExpr extends @booleanliteraltypeexpr, LiteralTypeExpr {
  predicate isTrue() { getValue() = "true" }
  predicate isFalse() { getValue() = "false" }
}

/**
 * An array type, such as `number[]`, or in general `T[]` where `T` is a type.
 *
 * This class includes only type expressions that use the notation `T[]`.
 * Named types such as `Array<number>` and tuple types such as `[number, string]`
 * are not array type expressions.
 */
class ArrayTypeExpr extends @arraytypeexpr, TypeExpr {
  /** Gets the type of the array elements. */
  TypeExpr getElementType() {
    result = getChildTypeExpr(0)
  }
}

/**
 * A union type, such as `string|number|boolean`.
 */
class UnionTypeExpr extends @uniontypeexpr, TypeExpr {
  /** Gets the `n`th type in the union, starting at 0. */
  TypeExpr getElementType(int n) {
    result = getChildTypeExpr(n)
  }

  /** Gets any of the types in the union. */
  TypeExpr getAnElementType() {
    result = getElementType(_)
  }

  /** Gets the number of types in the union. This is always at least two. */
  int getNumElementType() {
    result = count(getAnElementType())
  }
}

/**
 * A type of form `T[K]` where `T` and `K` are types.
 */
class IndexedAccessTypeExpr extends @indexedaccesstypeexpr, TypeExpr {
  /** Gets the type `T` in `T[K]`, denoting the object type whose properties are to be extracted. */
  TypeExpr getObjectType() {
    result = getChildTypeExpr(0)
  }

  /** Gets the type `K` in `T[K]`, denoting the property names to extract from the object type. */
  TypeExpr getIndexType() {
    result = getChildTypeExpr(1)
  }
}

/**
 * A type of form `S&T`, denoting the intersection of type `S` and type `T`.
 *
 * In general, there are can more than two operands to an intersection type.
 */
class IntersectionTypeExpr extends @intersectiontypeexpr, TypeExpr {
  /** Gets the `n`th operand of the intersection type, starting at 0. */
  TypeExpr getElementType(int n) {
    result = getChildTypeExpr(n)
  }

  /** Gets any of the operands to the intersection type. */
  TypeExpr getAnElementType() {
    result = getElementType(_)
  }

  /** Gets the number of operands to the intersection type. This is always at least two. */
  int getNumElementType() {
    result = count(getAnElementType())
  }
}

/**
 * A type expression enclosed in parentheses.
 */
class ParenthesizedTypeExpr extends @parenthesizedtypeexpr, TypeExpr {
  /** Gets the type inside the parentheses. */
  TypeExpr getElementType() {
    result = getChildTypeExpr(0)
  }

  override TypeExpr stripParens() {
    result = getElementType().stripParens()
  }
}

/**
 * A tuple type such as `[number, string]`.
 */
class TupleTypeExpr extends @tupletypeexpr, TypeExpr {
  /** Gets the `n`th element type in the tuple, starting at 0. */
  TypeExpr getElementType(int n) {
    result = getChildTypeExpr(n)
  }

  /** Gets any of the element types in the tuple. */
  TypeExpr getAnElementType() {
    result = getElementType(_)
  }

  /** Gets the number of elements in the tuple type. */
  int getNumElementType() {
    result = count(getAnElementType())
  }
}

/**
 * A type of form `keyof T` where `T` is a type.
 */
class KeyofTypeExpr extends @keyoftypeexpr, TypeExpr {
  /** Gets the type `T` in `keyof T`, denoting the object type whose property names are to be extracted. */
  TypeExpr getElementType() {
    result = getChildTypeExpr(0)
  }
}

/**
 * A type of form `{ [K in C]: T }` where `K in C` declares a type parameter with `C`
 * as the bound, and `T` is a type that may refer to `K`.
 */
class MappedTypeExpr extends @mappedtypeexpr, TypeParameterized, TypeExpr {
  /**
   * Gets the `K in C` part from `{ [K in C]: T }`.
   */
  TypeParameter getTypeParameter() {
    result = getChildTypeExpr(0)
  }

  override TypeParameter getTypeParameter(int n) {
    n = 0 and result = getTypeParameter()
  }

  /**
   * Gets the `T` part from `{ [K in C]: T }`.
   */
  TypeExpr getElementType() {
    result = getChildTypeExpr(1)
  }

  override string describe() {
    result = "mapped type"
  }
}

/**
 * A type of form `typeof E` where `E` is a possibly qualified name referring to a variable,
 * function, class, or namespace.
 */
class TypeofTypeExpr extends @typeoftypeexpr, TypeExpr {
  /**
   * Gets the `E` in `typeof E`, denoting the qualified the name of a
   * variable, function, class, or namespace whose type is to be extracted.
   */
  VarTypeAccess getExpressionName() { result = this.getChildTypeExpr(0) }
}

/**
 * A type of form `E is T` where `E` is a parameter name or `this`, and `T` is a type.
 *
 * This can only occur as the return type of a function type.
 */
class IsTypeExpr extends @istypeexpr, TypeExpr {
  /**
   * Gets the parameter name or `this` token `E` in `E is T`.
   */
  VarTypeAccess getParameterName() { result = this.getChildTypeExpr(0) }

  /**
   * Gets the type `T` in `E is T`.
   */
  TypeExpr getPredicateType() { result = this.getChildTypeExpr(1) }
}

/**
 * A possibly qualified name that refers to a variable from inside a type.
 *
 * This can occur as
 * - part of the operand to a `typeof` type, or
 * - as the first operand to an `is` type.
 *
 * For example, it may occur as the `E` in these examples:
 * ```
 * var x : typeof E
 * function f(...) : E is T {}
 * ```
 *
 * In the latter case, this may also refer to the pseudo-variable `this`.
 */
class VarTypeAccess extends @vartypeaccess, TypeExpr {
}

/**
 * An identifier that refers to a variable from inside a type.
 *
 * This can occur as part of the operand to a `typeof` type or as the first operand to an `is` type.
 */
class LocalVarTypeAccess extends @localvartypeaccess, VarTypeAccess, LexicalAccess, Identifier {
  /** Gets the variable being referenced, or nothing if this is a `this` keyword. */
  Variable getVariable() { bind(this, result) }
}

/**
 * A `this` keyword used as the first operand to an `is` type.
 *
 * For example, it may occur as the `this` in the following example:
 * ```
 * interface Node { isLeaf(): this is Leaf; }
 * ```
 */
class ThisVarTypeAccess extends @thisvartypeaccess, VarTypeAccess {}

/**
 * A qualified name that refers to a variable from inside a type.
 *
 * This can only occur as part of the operand to a `typeof` type.
 */
class QualifiedVarTypeAccess extends @qualifiedvartypeaccess, VarTypeAccess {
  /**
   * Gets the qualifier in front of the name being accessed, such as `http` in `http.ServerRequest`.
   */
  VarTypeAccess getQualifier() { result = getChildTypeExpr(0) }

  /**
   * Gets the last identifier in the name, such as `ServerRequest` in `http.ServerRequest`.
   */
  Identifier getIdentifier() { result = getChildTypeExpr(1) }
}

/**
 * A conditional type annotation, such as `T extends any[] ? A : B`.
 */
class ConditionalTypeExpr extends @conditionaltypeexpr, TypeExpr {
  /**
   * Gets the type to the left of the `extends` keyword, such as `T` in `T extends any[] ? A : B`.
   */
  TypeExpr getCheckType() { result = getChildTypeExpr(0) }

  /**
   * Gets the type to the right of the `extends` keyword, such as `any[]` in `T extends any[] ? A : B`.
   */
  TypeExpr getExtendsType() { result = getChildTypeExpr(1) }

  /**
   * Gets the type to be used if the `extend` condition holds, such as `A` in `T extends any[] ? A : B`.
   */
  TypeExpr getTrueType() { result = getChildTypeExpr(2) }

  /**
   * Gets the type to be used if the `extend` condition fails, such as `B` in `T extends any[] ? A : B`.
   */
  TypeExpr getFalseType() { result = getChildTypeExpr(3) }
}

/**
 * A type annotation of form `infer R`.
 */
class InferTypeExpr extends @infertypeexpr, TypeParameterized, TypeExpr {
  /**
   * Gets the type parameter capturing the matched type, such as `R` in `infer R`.
   */
  TypeParameter getTypeParameter() {
    result = getChildTypeExpr(0)
  }

  override TypeParameter getTypeParameter(int n) {
    n = 0 and result = getTypeParameter()
  }

  override string describe() {
    result = "'infer' type " + getTypeParameter().getName()
  }
}

/**
 * A scope induced by a conditional type expression whose `extends` type
 * contains `infer` types.
 */
class ConditionalTypeScope extends @conditionaltypescope, Scope {
  /** Gets the conditional type expression that induced this scope. */
  ConditionalTypeExpr getConditionalTypeExpr() {
    result = Scope.super.getScopeElement()
  }
}

/**
 * An expression with type arguments, occurring as the super-class expression of a class, for example:
 * ```
 * class StringList extends List<string>
 * ```
 * In the above example, `List` is a concrete expression, `string` is a type annotation,
 * and `List<string>` is thus an expression with type arguments.
 */
class ExpressionWithTypeArguments extends @expressionwithtypearguments, Expr {
  /**
   * Gets the expression, such as `List` in `List<string>`.
   *
   * Although it is common for this expression to take the form of a qualified name,
   * it can in general be any kind of expression.
   */
  Expr getExpression() { result = getChildExpr(-1) }

  /**
   * Gets the `n`th type argument, starting at 0.
   */
  TypeExpr getTypeArgument(int n) { result = getChildTypeExpr(n) }

  /**
   * Gets any of the type arguments.
   */
  TypeExpr getATypeArgument() { result = getTypeArgument(_) }

  /**
   * Gets the number of type arguments. This is always at least one.
   */
  int getNumTypeArgument() { result = count(getATypeArgument()) }

  override ControlFlowNode getFirstControlFlowNode() {
    result = getExpression().getFirstControlFlowNode()
  }
}

/**
 * A program element that supports type parameters, that is, a function, class, interface, type alias, mapped type, or `infer` type.
 */
class TypeParameterized extends @type_parameterized, ASTNode {
  /** Gets the `n`th type parameter declared on this function or type. */
  TypeParameter getTypeParameter(int n) { none() } // Overridden in subtypes.

  /** Gets any type parameter declared on this function or type. */
  TypeParameter getATypeParameter() { result = getTypeParameter(_) }

  /** Gets the number of type parameters declared on this function or type. */
  int getNumTypeParameter() { result = count(getATypeParameter()) }

  /** Holds if this function or type declares any type parameters. */
  predicate hasTypeParameters() { exists(getATypeParameter()) }

  /** Gets a description of this function or type. */
  string describe() { none() }
}

/**
 * A type parameter declared on a class, interface, function, or type alias.
 */
class TypeParameter extends @typeparameter, TypeExpr {
  /**
   * Gets the name of the type parameter as a string.
   */
  string getName() { result = getIdentifier().getName() }

  /**
   * Gets the identifier node of the type parameter, such as `T` in `class C<T>`.
   */
  Identifier getIdentifier() { result = getChildTypeExpr(0) }

  /**
   * Gets the upper bound of the type parameter, such as `U` in `class C<T extends U>`.
   */
  TypeExpr getBound() { result = getChildTypeExpr(1) }

  /**
   * Gets the default value of the type parameter, such as `D` in `class C<T = D>`.
   */
  TypeExpr getDefault() { result = getChildTypeExpr(2) }

  /**
   * Gets the function or type that declares this type parameter.
   */
  TypeParameterized getHost() { result.getATypeParameter() = this }

  /**
   * Gets the local type name declared by this type parameter.
   */
  LocalTypeName getLocalTypeName() {
      result = getIdentifier().(TypeDecl).getLocalTypeName()
  }
}

/**
 * A type assertion, also known as an unchecked type cast, is a TypeScript expression
 * of form `E as T` or `<T> E` where `E` is an expression and `T` is a type.
 */
class TypeAssertion extends Expr, @typeassertion {
  /** Gets the expression whose type to assert, that is, the `E` in `E as T` or `<T> E`. */
  Expr getExpression() { result = getChildExpr(0) }

  /** Gets the type to cast to, that is, the `T` in `E as T` or `<T> E`. */
  TypeExpr getTypeAnnotation() { result = getChildTypeExpr(1) }

  override ControlFlowNode getFirstControlFlowNode() {
    result = getExpression().getFirstControlFlowNode()
  }
}

/**
 * A type assertion specifically of the form `E as T` (as opposed to the `<T> E` syntax).
 */
class AsTypeAssertion extends TypeAssertion, @astypeassertion {}

/**
 * A type assertion specifically of the form `<T> E` (as opposed to the `E as T` syntax).
 */
class PrefixTypeAssertion extends TypeAssertion, @prefixtypeassertion {}

/**
 * A TypeScript expression of form `E!`, asserting that `E` is not null.
 */
class NonNullAssertion extends Expr, @non_null_assertion {
  /** Gets the expression whose type to assert. */
  Expr getExpression() { result = getChildExpr(0) }

  override ControlFlowNode getFirstControlFlowNode() {
    result = getExpression().getFirstControlFlowNode()
  }
}

/**
 * A possibly qualified identifier that refers to or declares a local name for a namespace.
 */
abstract class NamespaceRef extends ASTNode {}

/**
 * An identifier that declares a local name for a namespace, that is,
 * the name of an actual namespace declaration or the local name of an import.
 *
 * For instance, this includes the `N` in each of the following examples:
 * ```
 * namespace N {}
 * import N = require('./lib')
 * import N from './lib'
 * import { N } from './lib'
 * import { X as N } from './lib'
 * import * as N from './lib'
 * ```
 */
class LocalNamespaceDecl extends VarDecl, NamespaceRef {
  LocalNamespaceDecl() {
    any(NamespaceDeclaration nd).getId() = this or
    any(ImportEqualsDeclaration im).getId() = this or
    any(ImportSpecifier im).getLocal() = this or
    any(EnumDeclaration ed).getIdentifier() = this
  }

  /** Gets the local name being declared. */
  LocalNamespaceName getLocalNamespaceName() {
    namespacedecl(this, result)
  }

  /**
   * Gets the canonical name of the namespace being defined or aliased by this name.
   */
  Namespace getNamespace() {
    result = NameResolution::getNamespaceFromDeclarationId(this)
  }
}

/**
 * A possibly qualified name that refers to a namespace from inside a type annotation.
 *
 * For example, in the type access `A.B.C`, the prefix `A.B` is a qualified namespace access, and
 * the prefix `A` is a local namespace access.
 *
 * *Expressions* that refer to namespaces are represented as `VarAccess` and `PropAccess` expressions,
 * as opposed to `NamespaceAccess`.
 */
class NamespaceAccess extends TypeExpr, NamespaceRef, @namespaceaccess {
  Identifier getIdentifier() { none() }

  /**
   * Gets the canonical name of the namespace being accessed.
   */
  Namespace getNamespace() {
    result = NameResolution::getNamespaceFromAccess(this)
  }
}

/**
 * An identifier that refers to a namespace from inside a type annotation.
 */
class LocalNamespaceAccess extends NamespaceAccess, LexicalAccess, Identifier, @localnamespaceaccess {
  override Identifier getIdentifier() { result = this }

  /** Gets the local name being accessed. */
  LocalNamespaceName getLocalNamespaceName() {
    namespacebind(this, result)
  }
}

/**
 * A qualified name that refers to a namespace from inside a type annotation.
 */
class QualifiedNamespaceAccess extends NamespaceAccess, @qualifiednamespaceaccess {
  NamespaceAccess getQualifier() { result = getChildTypeExpr(0) }
  override Identifier getIdentifier() { result = getChildTypeExpr(1) }
}

/**
 * A TypeScript enum declaration, such as the following declaration:
 * ```
 * enum Color { red = 1, green, blue }
 * ```
 */
class EnumDeclaration extends NamespaceDefinition, @enumdeclaration, AST::ValueNode {
  /** Gets the name of this enum, such as `E` in `enum E { A, B }`. */
  Identifier getIdentifier() {
    result = getChildExpr(0)
  }

  /** Gets the name of this enum as a string. */
  string getName() {
    result = getIdentifier().getName()
  }

  /**
   * Gets the variable holding the enumeration object.
   *
   * For example, this would be the variable `E` introduced by `enum E { A, B }`.
   *
   * If the enumeration is a `const enum` then this variable will not exist at runtime
   * and all uses of the variable will be constant-folded by the TypeScript compiler,
   * but the analysis models it as an ordinary variable.
   */
  Variable getVariable() {
    result = getIdentifier().(VarDecl).getVariable()
  }

  /**
   * Gets the local type name introduced by the enumeration.
   *
   * For example, this would be the type `E` introduced by `enum E { A, B }`.
   */
  LocalTypeName getLocalTypeName() {
    result = getIdentifier().(TypeDecl).getLocalTypeName()
  }

  /**
   * Gets the canonical name of the type being defined.
   */
  TypeName getTypeName() {
    result = NameResolution::getTypeNameFromDefinition(this)
  }

  /**
   * Gets the local namespace name introduced by the enumeration, for use in
   * types that reference the enum members directly.
   *
   * For example, in the type `E.A` below, the enum `E` is accessed through the
   * local namespace name `E`:
   * ```
   * enum E { A = 1, B = 2 }
   * var x: E.A = 1
   * ```
   */
  override LocalNamespaceName getLocalNamespaceName() {
    result = getIdentifier().(LocalNamespaceDecl).getLocalNamespaceName()
  }

  /** Gets the `n`th enum member, starting at 0, such as `A` or `B` in `enum E { A, B }`. */
  EnumMember getMember(int n) {
    properties(result, this, n + 1, _, _)
  }

  /** Gets the enum member with the given name, if any. */
  EnumMember getMemberByName(string name) {
    result = getAMember() and result.getName() = name
  }

  /** Gets any of the enum members. */
  EnumMember getAMember() {
    result = getMember(_)
  }

  /** Gets the number of enum members. */
  int getNumMember() {
    result = count(getAMember())
  }

  /** Gets the `n`th decorator applied to this enum declaration. */
  Decorator getDecorator(int n) {
    result = getChildExpr(-n - 1)
  }

  /** Gets a decorator applied to this enum declaration. */
  Decorator getADecorator() {
    result = getDecorator(_)
  }

  /** Gets the number of decorators applied to this enum declaration. */
  int getNumDecorator() {
    result = count(getADecorator())
  }

  /** Holds if this enumeration is declared with the `const` keyword. */
  predicate isConst() {
    isConstEnum(this)
  }

  override predicate isAmbient() {
    hasDeclareKeyword(this) or getParent().isAmbient()
  }

  override ControlFlowNode getFirstControlFlowNode() {
    result = getIdentifier()
  }
}

/**
 * A member of a TypeScript enum declaration, such as `red` in the following declaration:
 * ```
 * enum Color { red = 1, green, blue }
 * ```
 */
class EnumMember extends ASTNode, @enum_member {
  /**
   * Gets the name of the enum member, such as `off` in `enum State { on, off }`.
   *
   * Note that if the name of the member is written as a string literal,
   * a synthetic identifier node is created to represent the name.
   * In other words, the name will always be an identifier node.
   */
  Identifier getIdentifier() {
    result = getChildExpr(0)
  }

  /** Gets the name of the enum member as a string. */
  string getName() {
    result = getIdentifier().getName()
  }

  /** Gets the explicit initializer expression of this member, if any. */
  Expr getInitializer() {
    result = getChildExpr(1)
  }

  /** Gets the enum declaring this member. */
  EnumDeclaration getDeclaringEnum() {
    result.getAMember() = this
  }

  override string toString() {
    properties(this, _, _, _, result)
  }

  override ControlFlowNode getFirstControlFlowNode() {
    result = getIdentifier()
  }

  /**
   * Gets the name of the member prefixed by the declaring enum name.
   *
   * For example, the prefixed name of the `red` member below is `Color.red`:
   * ```
   * enum Color { red, green, blue }
   * ```
   */
  string getPrefixedName() {
    result = getDeclaringEnum().getName() + "." + getName()
  }

  /**
   * Gets the canonical name of the type defined by this enum member.
   */
  TypeName getTypeName() {
    result = NameResolution::getTypeNameFromDefinition(this)
  }
}

/**
 * Scope induced by an interface declaration, containing the type parameters declared on the interface.
 *
 * Interfaces that do not declare type parameters have no scope object.
 */
class InterfaceScope extends @interfacescope, Scope {
  override string toString() {
    result = "interface scope"
  }
}

/**
 * Scope induced by a type alias declaration, containing the type parameters declared the the alias.
 *
 * Type aliases that do not declare type parameters have no scope object.
 */
class TypeAliasScope extends @typealiasscope, Scope {
  override string toString() {
    result = "type alias scope"
  }
}

/**
 * Scope induced by a mapped type expression, containing the type parameter declared as part of the type.
 */
class MappedTypeScope extends @mappedtypescope, Scope {
  override string toString() {
    result = "mapped type scope"
  }
}

/**
 * Scope induced by an enum declaration, containing the names of its enum members.
 *
 * Initializers of enum members are resolved in this scope since they can reference
 * previously-defined enum members by their unqualified name.
 */
class EnumScope extends @enumscope, Scope {
  override string toString() {
    result = "enum scope"
  }
}

/**
 * Scope induced by a declaration of form `declare module "X" {...}`.
 */
class ExternalModuleScope extends @externalmodulescope, Scope {
  override string toString() {
    result = "external module scope"
  }
}

/**
 * A TypeScript comment of one of the two forms:
 * ```
 * /// <reference path="FILE.d.ts"/>
 * /// <reference types="NAME"/>
 * ```
 */
class ReferenceImport extends LineComment {
  string attribute;
  string value;

  ReferenceImport() {
    getFile().getFileType().isTypeScript() and
    exists (string regex | regex = "/\\s*<reference\\s+([a-z]+)\\s*=\\s*[\"']([^\"']*)[\"']\\s*/>\\s*" |
      attribute = getText().regexpCapture(regex, 1) and
      value = getText().regexpCapture(regex, 2)) and
    (attribute = "path" or attribute = "types")
  }

  /**
   * Gets the value of `path` or `types` attribute.
   */
  string getAttributeValue() { result = value }

  /**
   * Gets the name of the attribute, i.e. "`path`" or "`types`".
   */
  string getAttributeName() { result = attribute }

  /**
   * Gets the file referenced by this import.
   */
  File getImportedFile() { none() } // Overridden in subtypes.

  /**
   * Gets the top-level of the referenced file.
   */
  TopLevel getImportedTopLevel() { result.getFile() = getImportedFile() }
}

/**
 * A TypeScript comment of the form:
 * ```
 * /// <reference path="FILE.d.ts"/>
 * ```
 */
class ReferencePathImport extends ReferenceImport {
  ReferencePathImport() {
    attribute = "path"
  }

  override File getImportedFile() {
    result = this.(PathExpr).resolve()
  }
}

/**
 * Treats reference imports comments as path expressions without exposing
 * the methods from `PathExpr` on `ReferenceImport`.
 */
private class ReferenceImportAsPathExpr extends PathExpr {
  ReferenceImport reference;

  ReferenceImportAsPathExpr() { this = reference }

  override string getValue() { result = reference.getAttributeValue() }

  override Folder getSearchRoot(int priority) {
    result = reference.getFile().getParentContainer() and priority = 0
  }
}

/**
 * A TypeScript comment of the form:
 * ```
 * /// <reference types="NAME" />
 * ```
 */
class ReferenceTypesImport extends ReferenceImport {
  ReferenceTypesImport() {
    attribute = "types"
  }

  override File getImportedFile() {
    result = min (Folder nodeModules, int distance |
      findNodeModulesFolder(getFile().getParentContainer(), nodeModules, distance) |
      nodeModules.getFolder("@types").getFolder(value).getFile("index.d.ts")
      order by distance)
  }
}

/**
 * A folder where TypeScript finds declaration files for imported modules.
 *
 * Currently, this is any folder whose path ends with `node_modules/@types`.
 */
class TypeRootFolder extends Folder {
  TypeRootFolder() {
    exists (Folder nodeModules |
      nodeModules.getBaseName() = "node_modules" and
      nodeModules.getFolder("@types") = this)
  }

  /**
   * Gets the enclosing `node_modules` folder.
   */
  Folder getNodeModulesFolder() {
    result = getParentContainer()
  }

  /**
   * Gets the `d.ts` file correspnding to the given module name.
   *
   * Concretely, this is the file at `node_modules/@types/<moduleName>/index.d.ts` if it exists.
   */
  File getModuleFile(string moduleName) {
    result = getFolder(moduleName).getFile("index.d.ts")
  }

  /**
   * Gets the priority with which this type root folder should be used from within the given search root.
   */
  int getSearchPriority(Folder searchRoot) {
    findNodeModulesFolder(searchRoot, getNodeModulesFolder(), result)
  }
}

/// Types

/**
 * A static type in the TypeScript type system.
 *
 * Types are generally not associated with a specific location or AST node.
 * For instance, there may be many AST nodes representing different uses of the
 * `number` keyword, but there only exists one `number` type.
 */
class Type extends @type {
  /**
   * Gets a string representation of this type.
   */
  string toString() { types(this, _, result) }

  /**
   * Gets the kind of this type, which is an integer value denoting how the
   * type is stored in the database.
   *
   * _Note_: The mapping from types to integers is considered an implementation detail
   * and may change between versions of the extractor.
   */
  int getKind() { types(this, result, _) }

  /**
   * Gets the `i`th child of this type.
   */
  Type getChild(int i) {
    type_child(result, this, i)
  }

  /**
   * Gets the type of the given property of this type.
   */
  Type getProperty(string name) {
    type_property(this, name, result)
  }

  /**
   * Gets the `n`th signature of the given kind present on this type.
   *
   * To get a signature of a specific kind, consider using `getFunctionSignature`, `getConstructorSignature`.
   *
   * Note that union and intersection types do not have signatures, even if their
   * elements contain signatures.
   */
  CallSignatureType getSignature(SignatureKind kind, int n) {
    type_contains_signature(this, kind.getId(), n, result)
  }

  /**
   * Gets a signature of the given kind.
   */
  CallSignatureType getASignature(SignatureKind kind) {
    type_contains_signature(this, kind.getId(), _, result)
  }

  /**
   * Gets the number of signatures of the given kind.
   */
  int getNumSignature(SignatureKind kind) {
    result = count(getASignature(kind))
  }

  /**
   * Gets the last signature of the given kind.
   *
   * When a signature is overloaded, the last signature is the most general version,
   * covering all cases but with less precision than the overloads.
   */
  CallSignatureType getLastSignature(SignatureKind kind) {
    result = getSignature(kind, getNumSignature(kind) - 1)
  }

  /**
   * Gets the `n`th function call signature.
   */
  FunctionCallSignatureType getFunctionSignature(int n) {
    type_contains_signature(this, _, n, result)
  }

  /**
   * Gets a function call signature.
   */
  FunctionCallSignatureType getAFunctionSignature() {
    type_contains_signature(this, _, _, result)
  }

  /**
   * Gets the number of function call signatures.
   */
  int getNumFunctionSignature() {
    result = count(getAFunctionSignature())
  }

  /**
   * Gets the last function call signature.
   *
   * When a signature is overloaded, the last signature is the most general version,
   * covering all cases but with less precision than the overloads.
   */
  FunctionCallSignatureType getLastFunctionSignature() {
      result = getFunctionSignature(getNumFunctionSignature() - 1)
  }

  /**
   * Gets the `n`th constructor call signature.
   */
  ConstructorCallSignatureType getConstructorSignature(int n) {
    type_contains_signature(this, _, n, result)
  }

  /**
   * Gets a constructor call signature.
   */
  ConstructorCallSignatureType getAConstructorSignature() {
    type_contains_signature(this, _, _, result)
  }

  /**
   * Gets the last constructor call signature.
   *
   * When a signature is overloaded, the last signature is the most general version,
   * covering all cases but with less precision than the overloads.
   */
  ConstructorCallSignatureType getLastConstructorSignature() {
    result = getConstructorSignature(getNumConstructorSignature() - 1)
  }

  /**
   * Gets the number of constructor call signatures.
   */
  int getNumConstructorSignature() {
    result = count(getAConstructorSignature())
  }
}

/**
 * A union type or intersection type, such as `string | number` or `T & U`.
 */
class UnionOrIntersectionType extends Type, @unionorintersectiontype {
  /**
   * Gets the `i`th member of this union or intersection, starting at 0.
   */
  Type getElementType(int i) {
    result = getChild(i)
  }

  /**
   * Gets a member of this union or intersection.
   */
  Type getAnElementType() {
    result = getElementType(_)
  }

  /**
   * Gets the number of elements in this union or intersection.
   */
  int getNumElementType() {
    result = count(getElementType(_))
  }
}

/**
 * A union type, such as `string | number`.
 *
 * Note that the `boolean` type is represented as the union `true | false`,
 * but is still displayed as `boolean` in string representations.
 */
class UnionType extends UnionOrIntersectionType, @uniontype {
}

/**
 * An intersection type, such as `T & {x: number}`.
 */
class IntersectionType extends UnionOrIntersectionType, @intersectiontype {
}

/**
 * A tuple type, such as `[number, string]`.
 */
class TupleType extends Type, @tupletype {
  /**
   * Gets the `i`th member of this tuple type, starting at 0.
   */
  Type getElementType(int i) {
    result = getChild(i)
  }

  /**
   * Gets a member of this tuple type.
   */
  Type getAnElementType() {
    result = getElementType(_)
  }

  /**
   * Gets the number of elements in this tuple type.
   */
  int getNumElementType() {
    result = count(getElementType(_))
  }
}

/**
 * The predefined `any` type.
 */
class AnyType extends Type, @anytype {}

/**
 * The predefined `string` type.
 */
class StringType extends Type, @stringtype {}

/**
 * The predefined `number` type.
 */
class NumberType extends Type, @numbertype {}

/**
 * The boolean literal type `true` or `false`.
 */
class BooleanLiteralType extends Type, @booleanliteraltype {
  /**
   * Gets the boolean value represented by this type.
   */
  boolean getValue() {
    if this instanceof @truetype then
      result = true
    else
      result = false
  }
}

/**
 * The `boolean` type, internally represented as the union type `true | false`.
 */
class BooleanType extends UnionType {
  BooleanType() {
    getAnElementType() instanceof @truetype and
    getAnElementType() instanceof @falsetype and
    count(getAnElementType()) = 2
  }
}

/**
 * The `void` type.
 */
class VoidType extends Type, @voidtype {}

/**
 * The `undefined` type.
 */
class UndefinedType extends Type, @undefinedtype {}

/**
 * The `null` type.
 */
class NullType extends Type, @nulltype {}

/**
 * The `never` type.
 */
class NeverType extends Type, @nevertype {}

/**
 * The `symbol` type or a specific `unique symbol` type.
 */
class SymbolType extends Type, @symboltype {}

/**
 * The `symbol` type.
 */
class PlainSymbolType extends SymbolType, @plainsymboltype {
}

/**
 * A `unique symbol` type.
 */
class UniqueSymbolType extends SymbolType, @uniquesymboltype {
  private NameResolution::Symbol getSymbol() {
    type_symbol(this, result)
  }

  /**
   * Gets the unqualified name of the variable exposing this symbol.
   */
  string getName() {
    result = getSymbol().getName()
  }

  /**
   * Holds if the variable exposing this symbol has the given global qualified name.
   */
  predicate hasQualifiedName(string globalName) {
    getSymbol().hasQualifiedName(globalName)
  }

  /**
   * Holds if the variable exposing this symbol is exported from an external module under the given name.
   */
  predicate hasQualifiedName(string moduleName, string exportedName) {
    getSymbol().hasQualifiedName(moduleName, exportedName)
  }
}

/**
 * The `object` type.
 */
class ObjectKeywordType extends Type, @objectkeywordtype {
}

/**
 * A type that refers to a class, interface, enum, or enum member.
 */
class TypeReference extends Type, @typereference {
  private NameResolution::Symbol getSymbol() {
    type_symbol(this, result)
  }

  /**
   * Gets a syntactic declaration of this named type.
   */
  TypeDefinition getADefinition() {
    ast_node_symbol(result, getSymbol())
  }

  /**
   * Gets the canonical name of the type being defined.
   */
  TypeName getTypeName() {
    result = getADefinition().getTypeName()
  }

  /**
   * Gets the `n`th type argument provided in this type, such as `string` in `Promise<string>`.
   */
  Type getTypeArgument(int n) {
    result = getChild(n)
  }

  /**
   * Gets a type argument provided in this type.
   */
  Type getATypeArgument() {
    result = getTypeArgument(_)
  }

  /**
   * Holds if type arguments are provided in this type.
   */
  predicate hasTypeArguments() {
    exists (getATypeArgument())
  }

  /**
   * Gets the number of type arguments provided in this type.
   */
  int getNumTypeArgument() {
    result = count(getTypeArgument(_))
  }

  /**
   * Holds if the referenced type has the given qualified name, rooted in the global scope.
   *
   * For example, `type.hasQualifiedName("React.Component")` holds if `type` is an instantiation
   * of the React `Component` class.
   */
  predicate hasQualifiedName(string globalName) {
    getSymbol().hasQualifiedName(globalName)
  }

  /**
   * Holds if the referenced type is exported from the given module under the given qualified name.
   *
   * For example, `type.hasQualifiedName("react", "Component")` holds if `type` is an instantiation
   * of the React `Component` class.
   */
  predicate hasQualifiedName(string moduleName, string exportedName) {
    getSymbol().hasQualifiedName(moduleName, exportedName)
  }
}

/**
 * A type that refers to a class, possibly with type arguments.
 */
class ClassType extends TypeReference {
  ClassDefinition declaration;

  ClassType() { declaration = getADefinition() }

  /**
   * Gets the declaration of the referenced class.
   */
  ClassDefinition getClass() { result = declaration }
}

/**
 * A type that refers to an interface, possibly with type arguents.
 */
class InterfaceType extends TypeReference {
  InterfaceDeclaration declaration;

  InterfaceType() { declaration = getADefinition() }

  /**
   * Gets the declaration of the referenced interface.
   */
  InterfaceDeclaration getInterface() { result = declaration }
}

/**
 * A type that refers to an enum.
 */
class EnumType extends TypeReference {
  EnumDeclaration declaration;

  EnumType() {
    declaration = getADefinition()
  }

  /**
   * Gets the declaration of the referenced enum.
   */
  EnumDeclaration getEnum() { result = declaration }
}

/**
 * A type that refers to the value of an enum member.
 */
class EnumLiteralType extends TypeReference {
  EnumMember declaration;

  EnumLiteralType() {
    declaration = getADefinition()
  }

  /**
   * Gets the declaration of the referenced enum member.
   */
  EnumMember getEnumMember() { result = declaration }
}

/**
 * An anonymous interface type, such as `{ x: number }`.
 */
class AnonymousInterfaceType extends Type, @objecttype {}

/**
 * A type that refers to a type variable.
 */
class TypeVariableType extends Type, @typevariabletype {}

/**
 * The type of a named value, `typeof X`, typically denoting the type of
 * a class constructor, namespace object, enum object, or module object.
 */
class TypeofType extends Type, @typeoftype {
  private NameResolution::Symbol getSymbol() {
    type_symbol(this, result)
  }

  /**
   * Gets the unqualified name of `X` in `typeof X`.
   */
  string getName() {
    result = getSymbol().getName()
  }

  /**
   * Holds if this refers to a value accessible by the global access path `globalName`.
   *
   * For example, `cls.hasQualifiedName("React.Component")` holds if `cls`
   * refers to the class constructor for `React.Component`.
   */
  predicate hasQualifiedName(string globalName) {
    getSymbol().hasQualifiedName(globalName)
  }

  /**
   * Holds if this refers to a value exported from `moduleName` under the access path `exportedName`.
   *
   * For example, `cls.hasQualifiedName("react", "Component")` holds if `cls`
   * refers to the class constructor for `Component` from the `react` module.
   *
   * The `exportedName` may an empty string if this refers to the module object itself.
   */
  predicate hasQualifiedName(string moduleName, string exportedName) {
    getSymbol().hasQualifiedName(moduleName, exportedName)
    or
    exportedName = "" and
    getSymbol().getExternalModuleName() = moduleName
  }

  override string toString() {
    // Avoid absolute path names in type strings.
    if exists (getSymbol().getExternalModuleName()) then
      result = "typeof module '" + getSymbol().getExternalModuleName() + "'"
    else if exists (getSymbol().getModule().getFile().getRelativePath()) then
      result = "typeof module '" + getSymbol().getModule().getFile().getRelativePath() + "'"
    else
      result = Type.super.toString()
  }
}

/**
 * One of two values indicating if a signature is a function or constructor signature.
 */
class SignatureKind extends string {
  SignatureKind() {
    this = "function" or this = "constructor"
  }

  /** Holds if this is the function call signature kind. */
  predicate isFunction() {
    this = "function"
  }

  /** Holds if this is the constructor call signature kind. */
  predicate isConstructor() {
    this = "constructor"
  }

  /**
   * For internal use.
   *
   * Gets the integer corresponding to this kind in the database.
   */
  int getId() {
    this = "function" and result = 0 or
    this = "constructor" and result = 1
  }
}

module SignatureKind {
  SignatureKind function() { result = "function" }
  SignatureKind constructor() { result = "constructor" }
}

/**
 * A function or constructor signature in a TypeScript type.
 */
class CallSignatureType extends @signature_type {
  /**
   * Gets a value indicating if this is a function or constructor signature.
   */
  SignatureKind getKind() {
    signature_types(this, result.getId(), _, _)
  }

  /**
   * Gets a string representation of this signature.
   */
  string toString() {
    signature_types(this, _, result, _)
  }

  /**
   * Gets the `n`th type contained in this signature, that is, a parameter or return type.
   *
   * The mapping from `n` to a given child is internal and may change between
   * versions of the extractor.
   */
  Type getChild(int n) {
    signature_contains_type(result, this, n)
  }

  /**
   * Gets a type contained in this signature, that is, the return type or a parameter type.
   */
  Type getAChildType() {
    result = getChild(_)
  }

  /**
   * Gets the return type of this signature.
   */
  Type getReturnType() {
    result = getChild(-1)
  }

  /**
   * Gets the type of the `n`th parameter of this signature.
   */
  Type getParameter(int n) {
    n >= 0 and result = getChild(n)
  }

  /**
   * Gets the type of a parameter of this signature.
   */
  Type getAParameter() {
    result = getParameter(_)
  }

  /**
   * Gets the number of parameters.
   */
  int getNumParameter() {
    result = count(getAParameter())
  }

  /**
   * Gets the number of required parameters, that is,
   * parameters that are not marked as optional with the `?` suffix.
   */
  int getNumRequiredParameter() {
    signature_types(this, _, _, result)
  }

  /**
   * Gets the number of optional parameters, that is,
   * parameters that are marked as optional with the `?` suffix.
   */
  int getNumOptionalParameter() {
    result = getNumParameter() - getNumRequiredParameter()
  }

  /**
   * Holds if the `n`th parameter is required, that is, it is not marked as
   * optional with the `?` suffix.
   */
  predicate isRequiredParameter(int n) {
    exists(getParameter(n)) and
    n <= getNumRequiredParameter()
  }

  /**
   * Holds if the `n`th parameter is declared optional with the `?` suffix.
   */
  predicate isOptionalParameter(int n) {
    exists(getParameter(n)) and
    n > getNumRequiredParameter()
  }

  /**
   * Gets the name of the `n`th parameter.
   */
  string getParameterName(int n) {
    signature_parameter_name(this, n, result)
  }

  /**
   * Gets the name of a parameter of this signature.
   */
  string getAParameterName() {
    result = getParameterName(_)
  }
}

/**
 * A function call signature in a type, that is, a signature without the `new` keyword.
 */
class FunctionCallSignatureType extends CallSignatureType, @function_signature_type {}

/**
 * A constructor call signature in a type, that is, a signature with the `new` keyword.
 */
class ConstructorCallSignatureType extends CallSignatureType, @constructor_signature_type {}
