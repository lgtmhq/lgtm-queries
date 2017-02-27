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

/** Standard builtin types and modules */

import python

/** the Python major version number */
int major_version() {
    explicit_major_version(result)
    or
    not explicit_major_version(_) and
    /* If there is more than one version, prefer 2 for backwards compatibilty */
    (
        if py_flags_versioned("version.major", "2", "2") then
            result = 2
        else
            result = 3
    )
}

/** the Python minor version number */
int minor_version() {
    exists(string v | py_flags_versioned("version.minor", v, major_version().toString()) |
           result = v.toInt())

}

/** the Python micro version number */
int micro_version() {
    exists(string v | py_flags_versioned("version.micro", v, major_version().toString()) |
           result = v.toInt())
}

private predicate explicit_major_version(int v) {
    exists(string version |
        py_flags_versioned("language.version", version, _) |
        version.charAt(0) = "2" and v = 2
        or
        version.charAt(0) = "3" and v = 3
    )
}
