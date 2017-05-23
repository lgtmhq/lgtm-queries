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
 * @name Equals or hashCode on arrays
 * @description The 'equals' and 'hashCode' methods on arrays only consider object identity, not
 *              array contents, which is unlikely to be what is intended.
 * @kind problem
 * @problem.severity error
 * @precision very-high
 * @tags reliability
 *       correctness
 */
import java

from MethodAccess ma, Array recvtype, Method m
where recvtype = ma.getQualifier().getType()
  and m = ma.getMethod()
  and (
    m instanceof HashCodeMethod or
    (
      m instanceof EqualsMethod and
      haveIntersection(recvtype, (Array)ma.getArgument(0).getType())
    )
  )
select ma, "The " + m.getName() + " method on arrays only considers object identity and ignores array contents."
