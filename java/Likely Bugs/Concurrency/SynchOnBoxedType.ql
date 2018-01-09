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
 * @name Synchronization on boxed types or strings
 * @description Synchronizing on boxed types or strings may lead to
 *              deadlock since an instance of that type is likely to
 *              be shared between many parts of the program.
 * @kind problem
 * @problem.severity error
 * @precision very-high
 * @id java/sync-on-boxed-types
 * @tags reliability
 *       correctness
 *       concurrency
 *       language-features
 *       external/cwe/cwe-662
 */

import java

from SynchronizedStmt synch, Type type
where synch.getExpr().getType() = type
  and (type instanceof BoxedType or type instanceof TypeString)
select synch.getExpr(), "Do not synchronize on objects of type " + type + "."
