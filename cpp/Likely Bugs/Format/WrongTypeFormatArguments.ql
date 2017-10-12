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
 * @name Wrong type of arguments to formatting function
 * @description Calling a printf-like function with the wrong type of arguments causes unpredictable
 *              behavior.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @id cpp/wrong-type-format-argument
 * @tags reliability
 *       correctness
 *       external/cwe/cwe-686
 */

import default

/** Used to avoid reporting conflicts between a char
 * pointer type with specified signedness and an unspecified
 * char pointer (whose signedness is compiler-dependent).
 */
class SignedOrUnsignedCharPointerType extends CharPointerType {
  SignedOrUnsignedCharPointerType() {
    this.getBaseType().(CharType).isUnsigned() or
    this.getBaseType().(CharType).isSigned()
  }
}

pragma[noopt]
private predicate formattingFunctionCallExpectedType(FormattingFunctionCall ffc, int pos, Type expected) {
    exists(FormattingFunction f, int i, FormatLiteral fl |
      ffc instanceof FormattingFunctionCall and
      ffc.getTarget() = f and
      f.getFormatParameterIndex() = i and
      ffc.getArgument(i) = fl and
      fl.getConversionType(pos) = expected
    )
}

pragma[noopt]
predicate formatArgType(FormattingFunctionCall ffc, int pos, Type expected, Expr arg, Type actual) {
  formattingFunctionCallExpectedType(ffc, pos, expected) and
  ffc.getConversionArgument(pos) = arg and
  exists(Type t | t = arg.getActualType() and t.getUnspecifiedType() = actual)
}

pragma[noopt]
predicate formatOtherArgType(FormattingFunctionCall ffc, int pos, Type expected, Expr arg, Type actual) {
  (arg = ffc.getMinFieldWidthArgument(pos) or arg = ffc.getPrecisionArgument(pos)) and
  actual = arg.getActualType() and
  exists(IntType it | it instanceof IntType and it.isImplicitlySigned() and expected = it)
}

predicate trivialConversion(Type expected, Type actual) {
  formatArgType(_, _, expected, _, actual) and
  (
    expected instanceof VoidPointerType and actual instanceof PointerType
  or
    (expected instanceof VoidPointerType and actual instanceof FunctionPointerType and expected.getSize() = actual.getSize())
  or
    expected instanceof IntegralType and actual instanceof Enum
  or
    expected instanceof CharPointerType and actual instanceof SignedOrUnsignedCharPointerType
  or
    expected instanceof SignedOrUnsignedCharPointerType and actual instanceof CharPointerType
  or
    expected instanceof CharType and actual instanceof IntType
  or
    expected instanceof UnsignedCharType and actual instanceof IntType
  or
    expected.(IntegralType).getSize() = actual.(IntegralType).getSize()
  or
    expected = actual
  )
}

int sizeof_IntType() {
  exists(IntType it | result = it.getSize())
}

from FormattingFunctionCall ffc, int n, Expr arg, Type expected, Type actual
where (
        (
          formatArgType(ffc, n, expected, arg, actual) and
          not trivialConversion(expected, actual)
        )
        or
        (
          formatOtherArgType(ffc, n, expected, arg, actual) and
          not actual.(IntegralType).getSize() = sizeof_IntType()
        )
      )
      and not arg.isAffectedByMacro()
select arg, "This argument should be of type "+expected.getName()+" but is of type "+actual.getName()
