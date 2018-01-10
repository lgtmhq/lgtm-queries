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

/** Provides internal predicates for working with files and folders. */

/**
 * For internal use.
 *
 * Gets the priority with which a given file extension should be found by module resolution.
 * Extensions with a lower numeric priority value are preferred.
 *
 * File types that compile to `js` are preferred over the `js` file type itself.
 * This is to ensure we find the original source file in case the compiled output is also present.
 */
int getFileExtensionPriority(string ext) {
  ext = "tsx" and result = 0 or
  ext = "ts" and result = 1 or
  ext = "jsx" and result = 2 or
  ext = "es6" and result = 3 or
  ext = "es" and result = 4 or
  ext = "mjs" and result = 5 or
  ext = "js" and result = 6 or
  ext = "json" and result = 7 or
  ext = "node" and result = 8
}
