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
 * @name Dangerous use of 'cin'
 * @description Using `cin` without specifying the length of the input
 *              may be dangerous.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @id cpp/dangerous-cin
 * @tags reliability
 *       security
 *       external/cwe/cwe-676
 *       external/cwe/cwe-242
 */
import cpp

/**
 * A C/C++ `char*` or `wchar_t*` type.
 */
class AnyCharPointerType extends PointerType {
  AnyCharPointerType() {
    this.getBaseType().getUnderlyingType() instanceof CharType or
    this.getBaseType().getUnderlyingType() instanceof WideCharType
  }
}

/**
 * A C/C++ `char[]` or `wchar_t[]` type.
 */
class AnyCharArrayType extends ArrayType {
  AnyCharArrayType() {
    this.getBaseType().getUnderlyingType() instanceof CharType or
    this.getBaseType().getUnderlyingType() instanceof WideCharType
  }
}

/**
 * A C++ `std::basic_string` type (the underlying type of `std::string`
 * and `std::wstring`).
 */
class AnyStdStringType extends Type {
  AnyStdStringType() {
    exists(Namespace std |
      std.getName() = "std" and
      std.getADeclaration() = this
    ) and
    this.getName().matches("basic\\_string<%")
  }
}

/**
 * A C++ `std::basic_ifstream` type (the underlying type of
 * `std::ifstream` and `std::wifstream`).
 */
class IFStream extends Type {
  IFStream() {
    exists(Namespace std |
      std.getName() = "std" and
      std.getADeclaration() = this
    ) and
    this.getName().matches("basic\\_ifstream<%")
  }
}

/**
 * The variable `std::cin` or `std::wcin`.
 */
class CinVariable extends NamespaceVariable {
  CinVariable() {
    (
      getName() = "cin" or
      getName() = "wcin"
    ) and
    getNamespace().getName() = "std"
  }
}

/** A call to `std::operator>>`. */
class OperatorRShiftCall extends FunctionCall {
  OperatorRShiftCall() {
    getTarget().getNamespace().getName() = "std" and
    getTarget().hasName("operator>>")
  }

  /*
     This is complicated by the fact this overload can be made
     in two ways:
      - as a member of the `std::istream` class, with one parameter.
      - as an independent function, with two parameters.
  */

  Expr getSource() {
    if (getTarget() instanceof MemberFunction) then (
      result = getQualifier()
    ) else (
      result = getArgument(0)
    )
  }

  Expr getDest() {
    if (getTarget() instanceof MemberFunction) then (
      result = getArgument(0)
    ) else (
      result = getArgument(1)
    )
  }
}

/**
 * A potentially dangerous `std::istream` or `std::wistream`, for
 * example, an access to `std::cin`.
 */
abstract class PotentiallyDangerousInput extends Expr {
  /**
   * Gets the variable that is the source of this input stream, if
   * it can be determined.
   */
  abstract Variable getStreamVariable();

  /**
   * Gets the previous access to the same input stream, if any.
   */
  abstract PotentiallyDangerousInput getPreviousAccess();

  /**
   * Gets the width restriction that applies to the input stream
   * for this expression, if any.
   */
  Expr getWidth() {
    result = getPreviousAccess().getWidthAfter()
  }

  private Expr getWidthSetHere() {
    exists(FunctionCall widthCall |
      // std::istream.width or std::wistream.width
      widthCall.getQualifier() = this and
      widthCall.getTarget().getName() = "width" and
      result = widthCall.getArgument(0)
    ) or exists(FunctionCall setwCall, Function setw |
      // >> std::setw
      setwCall = this.(OperatorRShiftCall).getDest() and
      setw = setwCall.getTarget() and
      setw.getNamespace().getName() = "std" and
      setw.hasName("setw") and
      result = setwCall.getArgument(0)
    )
  }

  private predicate isWidthConsumedHere() {
    // std::cin >> s, where s is a char*, char[] or std::string type
    // or wide character equivalent
    exists(Type t |
           t = this.(OperatorRShiftCall).getDest().getUnderlyingType() |
           t instanceof AnyCharPointerType or
           t instanceof AnyCharArrayType or
           t instanceof AnyStdStringType)
  }

  /**
   * Gets the width restriction that applies to the input stream
   * after this expression, if any.
   */
  Expr getWidthAfter() {
    result = getWidthSetHere()
    or
    (
      not exists(getWidthSetHere()) and
      not isWidthConsumedHere() and
      result = getWidth()
    )
  }
}

predicate nextPotentiallyDangerousInput(ControlFlowNode cfn, PotentiallyDangerousInput next, Variable streamVariable) {
  (
    // this node
    next = cfn and
    next.getStreamVariable() = streamVariable
  ) or (
    // flow
    not cfn.(PotentiallyDangerousInput).getStreamVariable() = streamVariable and
    nextPotentiallyDangerousInput(cfn.getASuccessor(), next, streamVariable)
  )
}

/**
 * A direct access to `std::cin` or `std::wcin`.
 */
class CinAccess extends PotentiallyDangerousInput {
  CinAccess() {
    this.(VariableAccess).getTarget() instanceof CinVariable
  }

  Variable getStreamVariable() {
    result = this.(VariableAccess).getTarget()
  }

  PotentiallyDangerousInput getPreviousAccess() {
    nextPotentiallyDangerousInput(result.getASuccessor(), this, result.getStreamVariable())
  }
}

/**
 * A direct access to a variable of type `std::ifstream` or `std::wifstream`.
 */
class IFStreamAccess extends PotentiallyDangerousInput {
  IFStreamAccess() {
    this.(VariableAccess).getTarget().getUnderlyingType() instanceof IFStream
  }

  Variable getStreamVariable() {
    result = this.(VariableAccess).getTarget()
  }

  PotentiallyDangerousInput getPreviousAccess() {
    nextPotentiallyDangerousInput(result.getASuccessor(), this, result.getStreamVariable())
  }
}

/**
 * A chained call to `std::operator>>` on a potentially dangerous input.
 */
class ChainedInput extends PotentiallyDangerousInput {
  ChainedInput() {
    this.(OperatorRShiftCall).getSource() instanceof PotentiallyDangerousInput
  }

  Variable getStreamVariable() {
    result = this.(OperatorRShiftCall).getSource().(PotentiallyDangerousInput).getStreamVariable()
  }

  PotentiallyDangerousInput getPreviousAccess() {
    result = this.(OperatorRShiftCall).getSource()
  }
}

from PotentiallyDangerousInput input, OperatorRShiftCall rshift, Expr dest
where
  // a call to operator>> on a potentially dangerous input
  input = rshift.getSource() and
  dest = rshift.getDest() and
  (
    (
      // destination is char* or wchar_t*
      dest.getUnderlyingType() instanceof AnyCharPointerType and

      // assume any width setting makes this safe
      not exists(input.getWidthAfter())
    ) or exists(int arraySize |
      // destination is char[] or wchar_t* or a wide character equivalent.
      arraySize = dest.getUnderlyingType().(AnyCharArrayType).getArraySize() and

      // assume any width setting makes this safe, unless we know
      // it to be larger than the array.
      forall(Expr w | w = input.getWidthAfter() |
        w.getValue().toInt() > arraySize
      )
    )
  )
select rshift, "Use of 'cin' without specifying the length of the input may be dangerous."
