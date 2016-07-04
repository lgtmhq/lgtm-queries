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
 * @name Exposing internal representation
 * @description An object that accidentally exposes its internal representation may allow the 
 *              object's fields to be modified in ways that the object is not prepared to handle.
 * @kind problem
 * @problem.severity recommendation
 * @cwe 485
 */
import java

predicate relevantType(RefType t) {
  t instanceof Array or
  exists(RefType sup | sup = t.getASupertype*() |
    sup.hasQualifiedName("java.util", "Map") or
    sup.hasQualifiedName("java.util", "Collection")
  )
}

predicate modifyMethod(Method m) {
  relevantType(m.getDeclaringType()) and (
    m.hasName("add") or m.hasName("addAll") or
    m.hasName("put") or m.hasName("putAll") or
    m.hasName("push") or m.hasName("pop") or
    m.hasName("remove") or m.hasName("removeAll") or
    m.hasName("clear") or m.hasName("set")
  )
}

predicate storesArray(Callable c, Field f) {
  f.getDeclaringType() = c.getDeclaringType().getASupertype*() and 
  relevantType(f.getType()) and
  exists(Parameter p | p = c.getAParameter() | f.getAnAssignedValue() = p.getAnAccess()) and
  not c.isStatic()
}

predicate returnsArray(Callable c, Field f) {
  f.getDeclaringType() = c.getDeclaringType().getASupertype*() and 
  relevantType(f.getType()) and
  exists(ReturnStmt rs | rs.getEnclosingCallable() = c and rs.getResult() = f.getAnAccess()) and
  not c.isStatic()
}

predicate mayWriteToArray(Expr modified) {
  writesToArray(modified) or
  
  // x = __y__; x[0] = 1;
  exists(AssignExpr e, LocalVariableDecl v | e.getDest() = v.getAnAccess() | 
    modified = e.getSource() and
    mayWriteToArray(v.getAnAccess())
  ) or
  
  // int[] x = __y__; x[0] = 1;
  exists(LocalVariableDeclExpr e, Variable v | e.getVariable() = v | 
    modified = e.getInit() and
    mayWriteToArray(v.getAnAccess())
  ) or
  
  // return __array__;    ...  method()[1] = 0
  exists(ReturnStmt rs | modified = rs.getResult() and relevantType(modified.getType()) |
    exists(Callable enclosing, MethodAccess ma |
      enclosing = rs.getEnclosingCallable() and ma.getMethod() = enclosing |
      mayWriteToArray(ma)
    )
  )
}

predicate writesToArray(Expr array) {
  relevantType(array.getType()) and
  (
    exists(Assignment a, ArrayAccess access | a.getDest() = access | access.getArray() = array)) or
    exists(MethodAccess ma | ma.getQualifier() = array | modifyMethod(ma.getMethod())
  )
}

/**
 * A successor of `s` that is either at the same level (e.g., the next statement
 * in a block) or further down (e.g., `s` is an `if` statement and the successor
 * is one of the branches).
 */
Stmt downwardSucc(Stmt s) {
  result = s.getASuccessor() and
  result.getParent+() = s.getParent()
}

VarAccess modificationAfter(Variable v, Stmt before) {
  mayWriteToArray(result) and
  result.getVariable() = v and
  result.getEnclosingStmt() = downwardSucc+(before) and
  exists(Expr access | mayWriteToArray(access) | access.getEnclosingStmt() = before)
}

Variable varPassedInto(Callable c, Stmt enclosingStmt) {
  exists(Call call | call.getCallee() = c |
    call.getAnArgument() = result.getAnAccess() and
    enclosingStmt = call.(Expr).getEnclosingStmt()
  )
}

predicate exposesByReturn(Callable c, Field f, Expr why, string whyText) {
  returnsArray(c, f) and
  exists(MethodAccess ma | ma.getMethod() = c and ma.getCompilationUnit() != c.getCompilationUnit() |
    mayWriteToArray(ma) and
    why = ma and
    whyText = "after this call to " + c.getName()
  )
}

predicate exposesByStore(Callable c, Field f, Expr why, string whyText) {
  storesArray(c, f) and
  exists(Variable v, Stmt enclosing |
    v = varPassedInto(c, enclosing) and
    enclosing.getCompilationUnit() != c.getCompilationUnit() and
    why = modificationAfter(v, enclosing) and
    whyText = "through the variable " + v.getName()
  )
}

from Callable c, Field f, Expr why, string whyText
where exposesByReturn(c, f, why, whyText) or
      exposesByStore(c, f, why, whyText)
select c, c.getName() + " exposes the internal representation stored in field " + f.getName() + 
          ". The value may be modified $@.", 
          why.getLocation(), whyText
