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
 * @name Javadoc has impossible 'throws' tag
 * @description Javadoc that incorrectly claims a method or constructor can throw an exception
 *              is misleading.
 * @kind problem
 * @problem.severity recommendation
 * @precision high
 * @id java/inconsistent-javadoc-throws
 * @tags maintainability
 */

import java

RefType getTaggedType(ThrowsTag tag) {
  result.hasName(tag.getExceptionName()) and
  exists(ImportType i | i.getFile() = tag.getFile() | i.getImportedType() = result)
}

predicate canThrow(Callable callable, RefType exception) {
  exists(string uncheckedException |
    uncheckedException = "RuntimeException" or uncheckedException = "Error" |
    exception.getASupertype*().hasQualifiedName("java.lang", uncheckedException)
  ) or
  callable.getAnException().getType().getASubtype*() = exception
}

from ThrowsTag throwsTag, RefType thrownType, Callable docMethod
where getTaggedType(throwsTag) = thrownType and
  docMethod.getDoc().getJavadoc().getAChild*() = throwsTag and
  not canThrow(docMethod, thrownType)
select throwsTag,
  "Javadoc for " + docMethod + " claims to throw " + thrownType.getName() + " but this is impossible."
