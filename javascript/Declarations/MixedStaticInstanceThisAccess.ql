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
* @name Wrong use of 'this' for static method
* @description A reference to a static method from within an instance method needs to be qualified with the class name, not `this`.
* @kind problem
* @problem.severity error
* @id js/mixed-static-instance-this-access
* @tags correctness
*       methods
* @precision high
*/
import javascript


/**
* Holds if `access` is in`fromMethod`, and it references `toMethod` through `this`.
*/
predicate isLocalMethodAccess(PropAccess access, MethodDefinition fromMethod, MethodDefinition toMethod) {
    fromMethod.getDeclaringClass() = toMethod.getDeclaringClass() and
    access.getEnclosingFunction() = fromMethod.getBody() and
    access.getBase() instanceof ThisExpr and
    access.getPropertyName() = toMethod.getName()
}

string getKind(MethodDefinition m) {
    if m.isStatic() then result = "static" else result = "instance"
}

from PropAccess access, MethodDefinition fromMethod, MethodDefinition toMethod, string fromKind, string toKind
where
    isLocalMethodAccess(access, fromMethod, toMethod) and
    fromKind = getKind(fromMethod) and
    toKind = getKind(toMethod) and
    toKind != fromKind and
    not toKind = fromKind and

    // exceptions
    not (
        // the class has a second member with the same name and the right kind
        exists (MethodDefinition toMethodWithSameKind |
            isLocalMethodAccess(access, fromMethod, toMethodWithSameKind) and
            fromKind = getKind(toMethodWithSameKind)
        )
        or
        // there is a dynamically assigned second member with the same name and the right kind
        exists (AnalyzedPropertyWrite apw, AbstractClass declaringClass, AbstractValue base |
          "static" = fromKind and base = declaringClass or
          "instance" = fromKind and base = TAbstractInstance(declaringClass) |
          declaringClass = TAbstractClass(fromMethod.getDeclaringClass()) and
          apw.writes(base, access.getPropertyName(), _)
        )
        or
        // the access is an assignment, probably deliberate
        access instanceof LValue
    )
select access, "Access to " + toKind + " method $@ from " + fromKind + " method $@ is not possible through `this`.", toMethod, toMethod.getName(), fromMethod, fromMethod.getName()
