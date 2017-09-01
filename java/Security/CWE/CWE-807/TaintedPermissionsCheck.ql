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
 * @name User-controlled data used in permissions check
 * @description Using user-controlled data in a permissions check may result in inappropriate
 *              permissions being granted.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @id java/tainted-permissions-check
 * @tags security
 *       external/cwe/cwe-807
 *       external/cwe/cwe-290
 */
import java
import semmle.code.java.security.DataFlow

class TypeShiroSubject extends RefType {
  TypeShiroSubject() {
    this.getQualifiedName() = "org.apache.shiro.subject.Subject"
  }
}

class TypeShiroWCPermission extends RefType {
  TypeShiroWCPermission() {
    this.getQualifiedName() = "org.apache.shiro.authz.permission.WildcardPermission"
  }
}

abstract class PermissionsConstruction extends Top {
  abstract Expr getInput();
}

class PermissionsCheckMethodAccess extends MethodAccess, PermissionsConstruction {
  PermissionsCheckMethodAccess() {
    exists(Method m | m = this.getMethod() |
      (m.getDeclaringType() instanceof TypeShiroSubject
      and m.getName() = "isPermitted")
      or
      (m.getName().toLowerCase().matches("%permitted%") and
      m.getNumberOfParameters() = 1)
    )
  }
  
  Expr getInput() {
    result = getArgument(0)
  }
  
  string toString() {
    result = MethodAccess.super.toString()
  }
}

class WCPermissionConstruction extends ClassInstanceExpr, PermissionsConstruction {
  WCPermissionConstruction() {
    this.getConstructor().getDeclaringType() instanceof TypeShiroWCPermission
  }
  
  Expr getInput() {
    result = getArgument(0)
  }
  
  string toString() {
    result = ClassInstanceExpr.super.toString()
  }
}

from UserInput u, PermissionsConstruction p
where u.flowsTo(p.getInput())
select p, "Permissions check uses user-controlled $@.", u, "data"
