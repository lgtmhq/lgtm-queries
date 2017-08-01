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
 * @name Password in configuration file
 * @description Storing unencrypted passwords in configuration files is unsafe.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @id js/password-in-configuration-file
 * @tags security
 *       external/cwe/cwe-256
 *       external/cwe/cwe-260
 *       external/cwe/cwe-313
 */

import javascript

/**
 * Holds if some JSON or YAML file contains a property with name `key`
 * and value `val`, where `valElement` is the entity corresponding to the
 * value.
 *
 * Dependencies in `package.json` files are excluded by this predicate.
 */
predicate config(string key, string val, Locatable valElement) {
  exists (JSONObject obj |
    not exists(PackageJSON p | obj = p.getADependenciesObject(_)) |
    obj.getPropValue(key) = valElement and
    val = valElement.(JSONString).getValue()
  )
  or
  exists (YAMLMapping m, YAMLString keyElement |
    m.maps(keyElement, valElement) and
    key = keyElement.getValue() and
    val = valElement.(YAMLString).getValue()
  )
}

/**
 * Holds if file `f` should be excluded because it looks like it may be
 * a dictionary file, or a test or example.
 */
predicate exclude(File f) {
  f.getRelativePath().regexpMatch(".*(^|/)(lang(uage)?s?|locales?|tests?|examples?)/.*")
}

from string key, string val, Locatable valElement
where config(key, val, valElement) and val != "" and
      (key.toLowerCase() = "password"
       or
       key.toLowerCase() != "readme" and
       val.regexpMatch("(?is).*password\\s*=(?!\\s*;).*")) and
      not exclude(valElement.getFile())
select valElement, "Avoid plaintext passwords in configuration files."
