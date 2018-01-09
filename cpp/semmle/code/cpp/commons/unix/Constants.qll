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
 * Standard Unix constants.
 */
import cpp

bindingset[input]
int parseOctal(string input) {
  input.charAt(0) = "0"
  and
  result = strictsum(int ix
                    | ix in [0 .. input.length()]
                    | 8.pow(input.length() - (ix+1))*input.charAt(ix).toInt())
}

int s_isuid() {
  result = parseOctal("04000")
}

int s_isgid() {
  result = parseOctal("02000")
}

int s_isvtx() {
  result = parseOctal("01000")
}

int s_irusr() {
  result = parseOctal("0400")
}

int s_iwusr() {
  result = parseOctal("0200")
}

int s_ixusr() {
  result = parseOctal("0100")
}

int s_irwxu() {
  result = s_irusr().bitOr(s_iwusr()).bitOr(s_ixusr())
}

int s_irgrp() {
  result = s_irusr().bitShiftRight(3)
}

int s_iwgrp() {
  result = s_iwusr().bitShiftRight(3)
}

int s_ixgrp() {
  result = s_ixusr().bitShiftRight(3)
}

int s_irwxg() {
  result = s_irwxu().bitShiftRight(3)
}

int s_iroth() {
  result = s_irgrp().bitShiftRight(3)
}

int s_iwoth() {
  result = s_iwgrp().bitShiftRight(3)
}

int s_ixoth() {
  result = s_ixgrp().bitShiftRight(3)
}

int s_irwxo() {
  result = s_irwxg().bitShiftRight(3)
}

int o_accmode() {
  result = parseOctal("0003")
}

int o_rdonly() {
  result = parseOctal("00")
}

int o_wronly() {
  result = parseOctal("01")
}

int o_rdwr() {
  result = parseOctal("02")
}

int o_creat() {
  result = parseOctal("0100")
}

int o_excl() {
  result = parseOctal("0200")
}