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

import java
import semmle.code.java.frameworks.Properties
import semmle.code.java.frameworks.JAXB
import semmle.code.java.security.DataFlow
import semmle.code.java.security.SensitiveActions

/** Test code filter. */
predicate testMethod(Method m) {
  (
    m instanceof TestMethod 
    or
    m.getDeclaringType() instanceof TestClass
  ) and
  // Do report results in the Juliet tests.
  not m.getLocation().getFile().getFullName().matches("%CWE%")
}

/** Class for expressions that may represent 'sensitive' information */
class SensitiveSource extends FlowSource {
  SensitiveSource() {
    // SensitiveExpr is abstract, this lets us inherit from it without
    // being a technical subclass
    this instanceof SensitiveExpr
  }

  /** Holds if this source flows to the `sink`. */
  cached
  predicate flowsToCached(Expr sink) {
    this.flowsTo(sink)
  }
}

/** 
 *  Class representing entities that may be stored/written, with methods
 *  for finding values that are stored within them, and cases
 *  of the entity being stored.
 */
abstract class Storable extends FlowSource {
  /** Gets an "input" that is stored in an instance of this class. */
  abstract Expr getAStore();
  
  /** Gets an expression where an instance of this class is stored (e.g. to disk). */
  abstract Expr getAnInput();
}

/** The instantiation of a cookie, which can act as storage. */
class Cookie extends Storable, ClassInstanceExpr {
  Cookie() {
    this.getConstructor().getDeclaringType().getQualifiedName() = "javax.servlet.http.Cookie"
  }
  
  /** Gets an input, for example `input` in `new Cookie("...", input);`. */
  Expr getAnInput() {
    result = this.getArgument(1)
  }
  
  /** Gets a store, for example `response.addCookie(cookie);`. */
  Expr getAStore() {
    exists(MethodAccess m, Method def | 
      m.getMethod() = def
      and def.getName() = "addCookie"
      and def.getDeclaringType().getQualifiedName() = "javax.servlet.http.HttpServletResponse"
      and result = m
      and this.flowsTo(m.getAnArgument())
    )
  }
  
  Callable getEnclosingCallable() { result = ClassInstanceExpr.super.getEnclosingCallable() }
  Stmt getEnclosingStmt() { result = ClassInstanceExpr.super.getEnclosingStmt() }
  
  string toString() {
    result = ClassInstanceExpr.super.toString()
  }
}

/** The instantiation of a `Properties` object, which can be stored to disk. */
class Properties extends Storable, ClassInstanceExpr {
  Properties() {
    this.getConstructor().getDeclaringType() instanceof TypeProperty
  }
  
  /** Gets an input, for example `input` in `props.setProperty("password", input);`. */
  Expr getAnInput() {
    exists(MethodAccess m |
      m.getMethod() instanceof PropertiesSetPropertyMethod
      and result = m.getArgument(1)
      and this.flowsTo(m.getQualifier())
    )
  }
  
  /** Gets a store, for example `props.store(outputStream, "...")`. */
  Expr getAStore() {
    exists(MethodAccess m |
      m.getMethod() instanceof PropertiesStoreMethod
      and result = m
      and this.flowsTo(m.getQualifier())
    )
  }
  
  Callable getEnclosingCallable() { result = ClassInstanceExpr.super.getEnclosingCallable() }
  Stmt getEnclosingStmt() { result = ClassInstanceExpr.super.getEnclosingStmt() }
  
  string toString() {
    result = ClassInstanceExpr.super.toString()
  }
}

abstract class ClassStore extends Storable, ClassInstanceExpr {
  string toString() {
    result = ClassInstanceExpr.super.toString()
  }
}

/** Gets an input, for example `input` in `instance.password = input`. */
private Expr getInstanceInput(ClassInstanceExpr instance) {
  // Currently taints all instances if data is ever assigned.
  exists(Field f |
    f.getDeclaringType() = instance.getConstructor().getDeclaringType()
    and result = f.getAnAssignedValue()
  )
}

/**
 * The instantiation of a serializable class, which can be stored to disk.
 *
 * Only includes tainted instances where data from a `SensitiveSource` may flow
 * to an input of the `Serializable`.
 */
class Serializable extends ClassStore {
  Serializable() {
    this.getConstructor().getDeclaringType().getASupertype*() instanceof TypeSerializable
    // `Properties` are `Serializable`, but handled elsewhere.
    and not this instanceof Properties
    // restrict attention to tainted instances
    and exists(SensitiveSource data | data.flowsToCached(getInstanceInput(this)))
  }
  
  /** Gets an input, for example `input` in `instance.password = input`. */
  Expr getAnInput() {
    result = getInstanceInput(this)
  }
  
  /** Gets a store, for example `outputStream.writeObject(instance)`. */
  Expr getAStore() {
    exists(MethodAccess m |
      result = m
      and m.getMethod() instanceof WriteObjectMethod
      and this.flowsTo(m.getArgument(0))
    )
  }
}

/** The instantiation of a marshallable class, which can be stored to disk as XML. */
class Marshallable extends ClassStore {
  Marshallable() {
    this.getConstructor().getDeclaringType() instanceof JAXBElement
  }
  
  /** Gets an input, for example `input` in `instance.password = input`. */
  Expr getAnInput() {
    result = getInstanceInput(this)
  }
  
  /** Gets a store, for example `marshaller.marshal(instance)`. */
  Expr getAStore() {
    exists(MethodAccess m |
      result = m
      and m.getMethod() instanceof JAXBMarshalMethod
      and this.flowsTo(m.getArgument(0))
    )
  }
}
