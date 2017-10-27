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

/**
 * A TypeScript interface declaration, inline interface type, or function type.
 */
class InterfaceDefinition extends @interfacedefinition, ClassOrInterface {}

/** A TypeScript interface declaration. */
class InterfaceDeclaration extends Stmt, InterfaceDefinition, @interfacedeclaration {
  override Identifier getIdentifier() {
    result = getChild(0)
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
      result = getChildTypeExpr(-(n+1)) and n >= 0
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
 * A TypeScript function type, such as `(x: string) => number`.
 *
 * Function types are treated as interfaces that contain a single call signature member.
 * For example, the type
 * ```
 * (x: number) => string
 * ```
 * is represented as
 * ```
 * { (x: number): string; }
 * ```
 */
class FunctionTypeExpr extends TypeExpr, InterfaceDefinition, @functiontypeexpr {
  override Identifier getIdentifier() { none() }

  override StmtContainer getContainer() {
    result = TypeExpr.super.getContainer()
  }

  override string describe() {
    result = "function type"
  }

  /** Holds if this is a constructor type, such as `new(x: number) => Object` */
  predicate isConstructorType() { getCallSignature() instanceof ConstructorCallSignature }

  /** Gets the implicit call signature defined by the function type. */
  CallSignature getCallSignature() { result = getACallSignature() }

  /** Gets the function AST node that holds the parameters and return type. */
  FunctionExpr getFunction() { result = getCallSignature().getBody() }

  /** Gets the `n`-th parameter of this function type. */
  Parameter getParameter(int n) { result = getFunction().getParameter(n) }

  /** Gets any of the parameters of this function type. */
  Parameter getAParameter() { result = getFunction().getAParameter() }

  /** Gets the number of parameters of this function type. */
  int getNumParameter() { result = getFunction().getNumParameter() }

  /** Gets the return type of this function type, if any. */
  TypeExpr getReturnTypeAnnotation() { result = getFunction().getReturnTypeAnnotation() }
}

/** A possibly qualified identifier that declares or refers to a type. */
abstract class TypeRef extends ASTNode {
}

/** The identifier declaring the name of a class or interface declaration. */
class TypeDecl extends TypeRef, Identifier {
  ClassOrInterface declaredType;

  TypeDecl() {
    this = declaredType.getIdentifier()
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

  /** Holds if this is the `Function` type. */
  predicate isRawFunction() { none() }

  /** Holds if this is the `object` type. */
  predicate isObjectKeyword() { none() }

  /** Gets this type expression, with any surrounding parentheses removed. */
  TypeExpr stripParens() {
    result = this
  }

  override predicate isAmbient() { any() }
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
  GenericTypeExpr getAsGenericType() { result.getTypeName() = this }

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
}

/** An identifier that is used as part of a type, such as `Date`. */
class SimpleTypeAccess extends @simpletypeaccess, TypeAccess, Identifier {
  override predicate isStringy() { getName() = "String" }
  override predicate isNumbery() { getName() = "Number" }
  override predicate isBooleany() { getName() = "Boolean" }
  override predicate isRawFunction() { getName() = "Function" }

  override Identifier getIdentifier() { result = this }
}

/**
 * A qualified name that is used as part of a type, such as `http.ServerRequest`.
 */
class QualifiedTypeAccess extends @qualifiedtypeaccess, TypeAccess {
  /**
   * Gets the qualifier in front of the name, such as `http` in `http.ServerRequest`.
   *
   * If the prefix consists of multiple identifiers, the qualifier is itself a qualified type access.
   * For example, the qualifier of `lib.util.List` is `lib.util`.
   */
  TypeAccess getQualifier() { result = getChildTypeExpr(0) }

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
  TypeAccess getTypeName() { result = getChildTypeExpr(-1) }

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
class SimpleVarTypeAccess extends @simplevartypeaccess, VarTypeAccess, Identifier {
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
