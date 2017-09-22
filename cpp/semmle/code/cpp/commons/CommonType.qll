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

import semmle.code.cpp.Type

/**
 * The C/C++ char* type.
 */
class CharPointerType extends PointerType {

  CharPointerType() { this.getBaseType() instanceof CharType }

}

/**
 * The C/C++ int* type.
 */
class IntPointerType extends PointerType {

  IntPointerType() { this.getBaseType() instanceof IntType }

}


/**
 * The C/C++ void* type.
 */
class VoidPointerType extends PointerType {

  VoidPointerType() { this.getBaseType() instanceof VoidType }

}

/**
 * The C/C++ size_t type.
 */
class Size_t extends IntegralType {
  Size_t() { this.hasName("size_t") }
}

/**
 * The C/C++ ssize_t type.
 */
class Ssize_t extends IntegralType {
  Ssize_t() { this.hasName("ssize_t") }
}

/**
 * The C/C++ ptrdiff_t type.
 */
class Ptrdiff_t extends IntegralType {
  Ptrdiff_t() { this.hasName("ptrdiff_t") }
}

/**
 * The C/C++ intmax_t type.
 */
class Intmax_t extends IntegralType {
  Intmax_t() { this.hasName("intmax_t") }
}

/**
 * The C/C++ uintmax_t type.
 */
class Uintmax_t extends IntegralType {
  Uintmax_t() { this.hasName("uintmax_t") }
}

/**
 * The C/C++ wchar_t type.
 */
class Wchar_t extends IntegralType {
  Wchar_t() { this.hasName("wchar_t") }
}