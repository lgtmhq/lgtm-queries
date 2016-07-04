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
 * @name Type variable hides another type
 * @description A type variable with the same name as another type that is in scope can cause
 *              the two types to be confused.
 * @kind problem
 * @problem.severity warning
 */

import default

RefType anOuterType(TypeVariable var) {
	var.getGenericCallable().getDeclaringType() = result
	or
	var.getGenericType() = result
	or
	result = anOuterType(var).(NestedType).getEnclosingType()
}

RefType aTypeVisibleFrom(TypeVariable var) {
	result = anOuterType(var)
	or
	exists(ImportType i | 
		var.getLocation().getFile() = i.getCompilationUnit() and
		result = i.getImportedType()
	)
	or
	(var.getPackage() = result.getPackage() and result instanceof TopLevelType)
}

from RefType hidden, TypeVariable var
where hidden = aTypeVisibleFrom(var)
  and var.getName() = hidden.getName()
select var, "Type $@ is hidden by this type variable.", hidden, hidden.getQualifiedName()
