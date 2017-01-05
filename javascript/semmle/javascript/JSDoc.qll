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

import Locations
import Comments

/**
 * A JSDoc comment.
 */
class JSDoc extends @jsdoc, Locatable {
  /** Get the description text of this JSDoc comment. */
  string getDescription() {
    jsdoc(this, result, _)
  }

  /** Get the raw comment this JSDoc comment is an interpretation of. */
  Comment getComment() {
    jsdoc(this, _, result)
  }

  /** Get a JSDoc tag within this JSDoc comment. */
  JSDocTag getATag() {
    result.getParent() = this
  }

  string toString() {
    result = getComment().toString()
  }
}

/**
 * A syntactic element that a JSDoc type expression may be nested in, that is,
 * either a JSDoc tag or another JSDoc type expression.
 */
class JSDocTypeExprParent extends @jsdoc_type_expr_parent {
  string toString() { none() }
}

/**
 * A JSDoc tag such as `@param Object options An object literal with options.` 
 */
class JSDocTag extends @jsdoc_tag, JSDocTypeExprParent, Locatable {
  /** Get the tag title; for instance, the title of a `@param` tag is `"param"`. */
  string getTitle() {
    jsdoc_tags (this, result, _, _, _)
  }

  /** The JSDoc comment this tag belongs to. */
  JSDoc getParent() {
    jsdoc_tags (this, _, result, _, _)
  }

  /** The index of this tag within its parent comment. */
  int getIndex() {
    jsdoc_tags (this, _, _, result, _)
  }

  string toString() {
    jsdoc_tags (this, _, _, _, result)
  }

  /** Get the description associated with the tag. */
  string getDescription() {
    jsdoc_tag_descriptions (this, result)
  }

  /**
   * Get the (optional) name associated with the tag, such as the name of the documented parameter
   * for a `@param` tag.
   */
  string getName() {
    jsdoc_tag_names (this, result)
  }

  /**
   * Get the (optional) type associated with the tag, such as the type of the documented parameter
   * for a `@param` tag.
   */
  JSDocTypeExpr getType() {
    result.getParent() = this
  }

  /** Does this tag document a simple name (as opposed to a name path)? */
  predicate documentsSimpleName() {
    exists (string name | name = getName() | not name.matches("%.%"))
  }
}

/**
 * A `@param` tag.
 */
class JSDocParamTag extends JSDocTag {
  JSDocParamTag() {
    getTitle().regexpMatch("param|arg(ument)?")
  }

  /** Get the parameter this tag refers to, if it can be determined. */
  Variable getDocumentedParameter() {
    exists (Parameterized parm | parm.getDocumentation() = getParent() |
      result = parm.getParameterVariable(getName())
    )
  }
}

/**
 * A JSDoc type expression.
 */
class JSDocTypeExpr extends @jsdoc_type_expr, JSDocTypeExprParent {
  /**
   * Get the syntactic element in which this type expression is nested, which may either
   * be another type expression or a JSDoc tag.
   */
  JSDocTypeExprParent getParent() {
    jsdoc_type_exprs (this, _, result, _, _)
  }

  /**
   * Get the index of this type expression within its parent.
   */
  int getIndex() {
    jsdoc_type_exprs (this, _, _, result, _)
  }

  /**
   * Get the `i`-th child type expression of this type expression.
   *
   * _Note_: the indices of child type expressions in their parent elements are an implementation
   * detail that may change between versions of the extractor.
   */
  JSDocTypeExpr getChild(int i) {
    jsdoc_type_exprs (result, _, this, i, _)
  }

  string toString() {
    jsdoc_type_exprs (this, _, _, _, result)
  }
}

/** An "any" type expression `*`. */
class JSDocAnyTypeExpr extends @jsdoc_any_type_expr, JSDocTypeExpr {}

/** A null type expression. */
class JSDocNullTypeExpr extends @jsdoc_null_type_expr, JSDocTypeExpr {}

/** A type expression representing the type of `undefined`. */
class JSDocUndefinedTypeExpr extends @jsdoc_undefined_type_expr, JSDocTypeExpr {}

/** A type expression representing an unknown type `?`. */
class JSDocUnknownTypeExpr extends @jsdoc_unknown_type_expr, JSDocTypeExpr {}

/** A type expression representing the void type. */
class JSDocVoidTypeExpr extends @jsdoc_void_type_expr, JSDocTypeExpr {}

/** A type expression referring to a named type. */
class JSDocNamedTypeExpr extends @jsdoc_named_type_expr, JSDocTypeExpr {
  /** Get the name of the type the expression refers to. */
  string getName() { result = toString() }
}

/**
 * An applied type expression such as `Array<string>`.
 */
class JSDocAppliedTypeExpr extends @jsdoc_applied_type_expr, JSDocTypeExpr {
  /** The head type expression, such as `Array` in `Array<string>`. */
  JSDocTypeExpr getHead() { result = getChild(-1) }

  /**
   * The i-th argument type of the applied type expression.
   *
   * For example, in `Array<string>`, `string` is the 0'th argument type.
   */
  JSDocTypeExpr getArgument(int i) { i >= 0 and result = getChild(i) }

  /**
   * Any argument type of the applied type expression.
   *
   * For example, in `Array<string>`, `string` is the only argument type.
   */
  JSDocTypeExpr getAnArgument() { result = getArgument(_) }
}

/**
 * A nullable type expression such as `?number`.
 */
class JSDocNullableTypeExpr extends @jsdoc_nullable_type_expr, JSDocTypeExpr {
  /** Get the argument type expression. */
  JSDocTypeExpr getTypeExpr() { result = getChild(0) }

  /** Is the `?` operator of this type expression written in prefix notation? */
  predicate isPrefix() { jsdoc_prefix_qualifier(this) }
}

/**
 * A non-nullable type expression such as `!number`.
 */
class JSDocNonNullableTypeExpr extends @jsdoc_non_nullable_type_expr, JSDocTypeExpr {
  /** Get the argument type expression. */
  JSDocTypeExpr getTypeExpr() { result = getChild(0) }

  /** Is the `!` operator of this type expression written in prefix notation? */
  predicate isPrefix() { jsdoc_prefix_qualifier(this) }
}

/**
 * A record type expression such as `{ x: number, y: string }`.
 */
class JSDocRecordTypeExpr extends @jsdoc_record_type_expr, JSDocTypeExpr {
  /** Get the name of the i-th field of the record type. */
  string getFieldName(int i) { jsdoc_record_field_name (this, i, result) }

  /** Get the name of some field of the record type. */
  string getAFieldName() { result = getFieldName(_) }

  /** Get the type of the i-th field of the record type. */
  JSDocTypeExpr getFieldType(int i) { result = getChild(i) }

  /** Get the type of the field with the given name. */
  JSDocTypeExpr getFieldTypeByName(string fieldname) {
    exists (int idx | fieldname = getFieldName(idx) and result = getFieldType(idx))
  }
}

/**
 * An array type expression such as `[string]`.
 */
class JSDocArrayTypeExpr extends @jsdoc_array_type_expr, JSDocTypeExpr {
  /** Get the type of the i-th element of this array type. */
  JSDocTypeExpr getElementType(int i) { result = getChild(i) }

  /** Get some element type of this array type. */
  JSDocTypeExpr getAnElementType() { result = getElementType(_) }
}

/**
 * A union type expression such as `number|string`.
 */
class JSDocUnionTypeExpr extends @jsdoc_union_type_expr, JSDocTypeExpr {
  /** Get one of the type alternatives of this union type. */
  JSDocTypeExpr getAnAlternative() { result = getChild(_) }
}

/**
 * A function type expression such as `function(string): number`.
 */
class JSDocFunctionTypeExpr extends @jsdoc_function_type_expr, JSDocTypeExpr {
  /** Get the result type of this function type. */
  JSDocTypeExpr getResultType() { result = getChild(-1) }

  /** Get the receiver type of this function type. */
  JSDocTypeExpr getReceiverType() { result = getChild(-2) }

  /** Get the i-th parameter type of this function type. */
  JSDocTypeExpr getParameterType(int i) { i >= 0 and result = getChild(i) }

  /** Get some parameter type of this function type. */
  JSDocTypeExpr getAParameterType() { result = getParameterType(_) }

  /** Is this function type a constructor type? */
  predicate isConstructorType() { jsdoc_has_new_parameter(this) }
}

/**
 * An optional parameter type such as `number=`.
 */
class JSDocOptionalParameterTypeExpr extends @jsdoc_optional_type_expr, JSDocTypeExpr {
  /** Get the underlying type of this optional type. */
  JSDocTypeExpr getUnderlyingType() { result = getChild(0) }
}

/**
 * A rest parameter type such as `string...`.
 */
class JSDocRestParameterTypeExpr extends @jsdoc_rest_type_expr, JSDocTypeExpr {
  /** Get the underlying type of this rest parameter type. */
  JSDocTypeExpr getUnderlyingType() { result = getChild(0) }
}

/**
 * An error encountered while parsing a JSDoc comment.
 */
class JSDocError extends @jsdoc_error {
  /** Get the tag that triggered the error. */
  JSDocTag getTag() {
    jsdoc_errors (this, result, _, _)
  }

  /** Get the message associated with the error. */
  string getMessage() {
    jsdoc_errors (this, _, result, _)
  }

  string toString() {
    jsdoc_errors (this, _, _, result)
  }
}