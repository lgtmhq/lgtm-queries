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

import java

predicate initializedToField(LocalVariableDecl d, Field f) {
  exists(LocalVariableDeclExpr e | e.getVariable() = d and f.getAnAccess() = e.getInit())
}

predicate getterFor(Method m, Field f) {
  m.getName().matches("get%") and
  m.getDeclaringType() = f.getDeclaringType() and
  exists(ReturnStmt ret | ret.getEnclosingCallable() = m and ret.getResult() = f.getAnAccess())
}

predicate setterFor(Method m, Field f) {
  m.getName().matches("set%") and
  m.getDeclaringType() = f.getDeclaringType() and
  f.getAnAssignedValue() = m.getAParameter().getAnAccess() and
  m.getNumberOfParameters() = 1
}

predicate shadows(LocalVariableDecl d, Class c, Field f, Callable method) {
  d.getCallable() = method and
  method.getDeclaringType() = c and
  c.getAField() = f and
  f.getName() = d.getName() and
  f.getType() = d.getType() and
  not d.getCallable().isStatic() and
  not f.isStatic()
}

predicate thisAccess(LocalVariableDecl d, Field f) {
  shadows(d, _, f, _) and
  exists(VarAccess va | va.getVariable().(Field).getSourceDeclaration() = f |
    va.getQualifier() instanceof ThisAccess and
    va.getEnclosingCallable() = d.getCallable()
  )
}

predicate confusingAccess(LocalVariableDecl d, Field f) {
  shadows(d, _, f, _) and
  exists(VarAccess va | va.getVariable().(Field).getSourceDeclaration() = f |
    not exists(va.getQualifier()) and
    va.getEnclosingCallable() = d.getCallable()
  )
}

predicate assignmentToShadowingLocal(LocalVariableDecl d, Field f) {
  shadows(d, _, _, _) and
  exists(Expr assignedValue, Expr use |
    d.getAnAssignedValue() = assignedValue and getARelevantChild(assignedValue) = use |
    exists(FieldAccess access, Field ff | access = assignedValue |
      ff = access.getField() and
      ff.getSourceDeclaration() = f
    ) or
    exists(MethodAccess get, Method getter | get = assignedValue and getter = get.getMethod() |
      getterFor(getter, f)
    )
  )
}

predicate assignmentFromShadowingLocal(LocalVariableDecl d, Field f) {
  shadows(d, _, _, _) and
  exists(VarAccess access | access = d.getAnAccess() |
    exists(MethodAccess set, Expr arg, Method setter | 
      access = getARelevantChild(arg) and 
      arg = set.getAnArgument() and
      setter = set.getMethod() and 
      setterFor(setter, f)
    ) or
    exists(Field instance, Expr assignedValue | 
      access = getARelevantChild(assignedValue) and 
      assignedValue = instance.getAnAssignedValue() and
      instance.getSourceDeclaration() = f
    )
  )
}

private
Expr getARelevantChild(Expr parent) {
  exists(MethodAccess ma | parent = ma.getAnArgument() and result = parent) or
  exists(Variable v | parent = v.getAnAccess() and result = parent) or
  exists(Expr mid | mid = getARelevantChild(parent) and result = mid.getAChildExpr())
}
