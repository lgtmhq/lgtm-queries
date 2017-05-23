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
 * @name Cleartext storage of sensitive information using 'Properties' class
 * @description Storing sensitive information in cleartext can expose it to an attacker.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @tags security
 *       external/cwe/cwe-313
 */
import java
import semmle.code.java.security.DataFlow
import SensitiveStorage

from SensitiveSource data, Properties s, Expr input, Expr store
where
  input = s.getAnInput()
  and store = s.getAStore()
  and data.flowsToCached(input)
  // Exclude results in test code.
  and not testMethod(store.getEnclosingCallable())
  and not testMethod(data.getEnclosingCallable())
select store, "'Properties' class $@ containing $@ is stored here. Data was added $@.", 
  s, s.toString(), 
  data, "sensitive data",
  input, "here"
