// Copyright 2016 Semmle Ltd.
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
 * @name Close output resource
 * @description A resource that is opened for writing but not closed may cause a resource 
 *              leak.
 * @kind problem
 * @problem.severity error
 * @cwe 404 772
 */
import CloseType

predicate writerType(RefType t) {
  exists(RefType sup | sup = t.getASupertype*() | 
    sup.hasName("Writer") or
    sup.hasName("OutputStream")
  )
}

predicate safeWriterType(RefType t) {
  exists(RefType sup | sup = t.getASupertype*() | 
    sup.hasName("StringWriter") or
    sup.hasName("ByteArrayOutputStream")
  )
}

from ClassInstanceExpr cie, RefType t
where badCloseableInit(cie) and
      cie.getType() = t and
      writerType(t) and
      not safeWriterType(typeInDerivation(cie)) and
      not noNeedToClose(cie)
select cie, "This " + t.getName() + " is not always closed on method exit."
