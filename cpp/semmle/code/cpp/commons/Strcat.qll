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

import cpp

/**
 * A function that concatenates the string from its second argument
 * to the string from its first argument, for example `strcat`.
 */
class StrcatFunction extends Function {
  StrcatFunction() {
    exists(string name | name = getName()|
      name = "strcat" // strcat(dst, src)
      or name = "strncat" // strncat(dst, src, max_amount)
      or name = "wcscat" // wcscat(dst, src)
      or name = "_mbscat" // _mbscat(dst, src)
      or name = "wcsncat" // wcsncat(dst, src, max_amount)
      or name = "_mbsncat" // _mbsncat(dst, src, max_amount)
      or name = "_mbsncat_l" // _mbsncat_l(dst, src, max_amount, locale)
    )
  }
}