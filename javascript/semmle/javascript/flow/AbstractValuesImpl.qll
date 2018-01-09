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
 * INTERNAL: This is an internal API and subject to change; queries should use
 * `AbstractValues.qll` and `InferredTypes.qll` instead.
 *
 * Provides a representation for abstract values.
 */

import AbstractValues
private import InferredTypes

/** An abstract value inferred by the flow analysis. */
newtype TAbstractValue =
  /** An abstract representation of `null`. */
  TAbstractNull()
  or
  /** An abstract representation of `undefined`. */
  TAbstractUndefined()
  or
  /** An abstract representation of Boolean value `b`. */
  TAbstractBoolean(boolean b) { b = true or b = false }
  or
  /** An abstract representation of the number zero. */
  TAbstractZero()
  or
  /** An abstract representation of a non-zero number. */
  TAbstractNonZero()
  or
  /** An abstract representation of the empty string. */
  TAbstractEmpty()
  or
  /** An abstract representation of a string that coerces to a number (and not `NaN`). */
  TAbstractNumString()
  or
  /** An abstract representation of a non-empty string that does not coerce to a number. */
  TAbstractOtherString()
  or
  /** An abstract representation of a function object corresponding to function `f`. */
  TAbstractFunction(Function f)
  or
  /** An abstract representation of a class object corresponding to class `c`. */
  TAbstractClass(ClassDefinition c)
  or
  /** An abstract representation of a Date object. */
  TAbstractDate()
  or
  /**
   * An abstract representation of the arguments object of a function object
   * corresponding to function `f`.
   */
  TAbstractArguments(Function f) { exists(f.getArgumentsVariable().getAnAccess()) }
  or
  /** An abstract representation of the global object. */
  TAbstractGlobalObject()
  or
  /** An abstract representation of a CommonJS `module` object. */
  TAbstractModuleObject(Module m) {
    // only interesting for modules that are imported somewhere
    m = any(Require r).getImportedModule()
  }
  or
  /** An abstract representation of a CommonJS `exports` object. */
  TAbstractExportsObject(Module m) {
    exists(TAbstractModuleObject(m))
  }
  or
  /** An abstract representation of all objects arising from an object literal expression. */
  TAbstractObjectLiteral(ObjectExpr oe)
  or
  /**
   * An abstract value representing all instances of a class or function `F`,
   * as well as the default prototype of `F` (that is, the initial value of
   * `F.prototype`).
   */
  TAbstractInstance(AbstractCallable ac) {
    ac instanceof AbstractClass
    or
    exists (Function f | ac = TAbstractFunction(f) | not f.isNonConstructible(_))
  }
  or
  /** An abstract representation of an object not covered by the other abstract values. */
  TAbstractOtherObject()
  or
  /**
   * An abstract representation of an indefinite value that represents a function or class,
   * where `cause` records the cause of the incompleteness.
   */
  TIndefiniteFunctionOrClass(DataFlowIncompleteness cause)
  or
  /**
   * An abstract representation of an indefinite value that represents an object,
   * but not a function or class, with `cause` recording the cause of the incompleteness.
   */
  TIndefiniteObject(DataFlowIncompleteness cause)
  or
  /**
   * Abstract representation of indefinite values that represent any value, with
   * `cause` recording the cause of the incompleteness.
   */
  TIndefiniteAbstractValue(DataFlowIncompleteness cause)

/**
 * Gets a definite abstract value with the given type.
 */
DefiniteAbstractValue abstractValueOfType(TypeTag type) {
  result.getType() = type
}
