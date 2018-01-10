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
 * @name Potential input resource leak
 * @description A resource that is opened for reading but not closed may cause a resource
 *              leak.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @id java/input-resource-leak
 * @tags efficiency
 *       correctness
 *       resources
 *       external/cwe/cwe-404
 *       external/cwe/cwe-772
 */
import CloseType

predicate readerType(RefType t) {
  exists(RefType sup | sup = t.getASupertype*() | 
    sup.hasName("Reader") or
    sup.hasName("InputStream") or
    sup.hasQualifiedName("java.util.zip", "ZipFile")
  )
}

predicate safeReaderType(RefType t) {
  exists(RefType sup | sup = t.getASupertype*() | 
    sup.hasName("StringReader") or
    sup.hasName("ByteArrayInputStream") or
    sup.hasName("StringInputStream")
  )
}

from ClassInstanceExpr cie, RefType t
where badCloseableInit(cie) and
      cie.getType() = t and
      readerType(t) and
      not safeReaderType(typeInDerivation(cie)) and
      not noNeedToClose(cie)
select cie, "This " + t.getName() + " is not always closed on method exit."
