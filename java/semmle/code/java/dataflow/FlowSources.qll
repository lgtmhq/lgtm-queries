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

import java
import semmle.code.java.dataflow.DataFlow
import semmle.code.java.dataflow.TaintTracking
import semmle.code.java.dataflow.DefUse
import semmle.code.java.frameworks.Jdbc
import semmle.code.java.frameworks.Networking
import semmle.code.java.frameworks.Properties
import semmle.code.java.frameworks.Rmi
import semmle.code.java.frameworks.Servlets
import semmle.code.java.frameworks.ApacheHttp
import semmle.code.java.frameworks.android.XmlParsing
import semmle.code.java.frameworks.android.WebView
import semmle.code.java.frameworks.JaxWS
import semmle.code.java.frameworks.android.Intent

/** Class for `tainted` user input. */
abstract class UserInput extends DataFlow::Node {}

private predicate variableStep(Expr tracked, VarAccess sink) {
  exists(VariableAssign def |
    def.getSource() = tracked and
    defUsePair(def, sink)
  )
}

/** Input that may be controlled by a remote user. */
class RemoteUserInput extends UserInput {
  RemoteUserInput() {
    this.asExpr().(MethodAccess).getMethod() instanceof RemoteTaintedMethod

    // Parameters to RMI methods.
    or exists (RemoteCallableMethod method |
       method.getAParameter() = this.asParameter()
       and (
         getType() instanceof PrimitiveType
         or getType() instanceof TypeString
       )
    )

    // Parameters to Jax WS methods.
    or exists (JaxWsEndpoint endpoint |
       endpoint.getARemoteMethod().getAParameter() = this.asParameter()
    )
    // Parameters to Jax Rs methods.
    or exists (JaxRsResourceClass service |
       service.getAnInjectableCallable().getAParameter() = this.asParameter() or
       service.getAnInjectableField().getAnAccess() = this.asExpr()
    )

    // Reverse DNS. Try not to trigger on `localhost`.
    or exists(MethodAccess m | m = this.asExpr() |
      m.getMethod() instanceof ReverseDNSMethod and
      not exists(MethodAccess l |
        (variableStep(l, m.getQualifier()) or l = m.getQualifier())
        and l.getMethod().getName() = "getLocalHost"
      )
    )

    //MessageBodyReader
    or exists(MessageBodyReaderRead m |
      m.getParameter(4) = this.asParameter() or
      m.getParameter(5) = this.asParameter()
    )
  }

  /**
   * Holds if taint can flow from this `RemoteUserInput` to `sink`.
   *
   * In addition to the basic taint flow, this allows a path to end in a number
   * of steps through instance fields.
   */
  predicate flowsTo(DataFlow::Node sink) {
    remoteUserInputFlow(this, sink)
  }
}

/**
 * Holds if taint can flow from `node1` to `node2` in either one local step or
 * through an instance field.
 */
private predicate localInstanceFieldStep(DataFlow::Node node1, DataFlow::Node node2) {
  TaintTracking::localTaintStep(node1, node2) or
  exists (InstanceField field |
    node1.asExpr() = field.getAnAssignedValue() or
    exists(Assignment assign | assign.getRhs() = node1.asExpr() |
      assign.getDest().(ArrayAccess).getArray() = field.getAnAccess()
    )
    |
    node2.asExpr() = field.getAnAccess()
  )
}

private class RemoteUserInputConfig extends TaintTracking::Configuration {
  RemoteUserInputConfig() { this = "FlowSources.qll:RemoteUserInputConfig" }
  override
  predicate isSource(DataFlow::Node source) { source instanceof RemoteUserInput }
  override
  predicate isSink(DataFlow::Node sink) { any() }
}

cached
private predicate remoteUserInputFlow(RemoteUserInput src, DataFlow::Node sink) {
  any(RemoteUserInputConfig config).hasFlow(src, sink) or
  exists(DataFlow::Node mid |
    remoteUserInputFlow(src, mid) and
    localInstanceFieldStep(mid, sink)
  )
}

/** Input that may be controlled by a local user. */
abstract class LocalUserInput extends UserInput {}

class EnvInput extends LocalUserInput {
  EnvInput() {
    // Parameters to a main method.
    exists (MainMethod main | this.asParameter() = main.getParameter(0))

    // Args4j arguments.
    or exists (Field f | this.asExpr() = f.getAnAccess() | f.getAnAnnotation().getType().getQualifiedName() = "org.kohsuke.args4j.Argument")

    // Results from various specific methods.
    or this.asExpr().(MethodAccess).getMethod() instanceof EnvTaintedMethod

    // Access to `System.in`.
    or exists(Field f | this.asExpr() = f.getAnAccess() | f instanceof SystemIn)

    // Access to files.
    or this.asExpr().(ConstructorCall).getConstructedType().hasQualifiedName("java.io", "FileInputStream")
  }
}

class DatabaseInput extends LocalUserInput {
  DatabaseInput() {
    this.asExpr().(MethodAccess).getMethod() instanceof ResultSetGetStringMethod
  }
}

private
class RemoteTaintedMethod extends Method {
  RemoteTaintedMethod() {
    this instanceof ServletRequestGetParameterMethod or
    this instanceof HttpServletRequestGetQueryStringMethod or
    this instanceof HttpServletRequestGetHeaderMethod or
    this instanceof HttpServletRequestGetPathMethod or
    this instanceof ServletRequestGetBodyMethod or
    this instanceof CookieGetValueMethod or
    this instanceof URLConnectionGetInputStreamMethod or
    this instanceof SocketGetInputStreamMethod or
    this instanceof ApacheHttpGetParams or
    this instanceof ApacheHttpEntityGetContent or
    // In the setting of Android we assume that XML has been transmitted over
    // the network, so may be tainted.
    this instanceof XmlPullGetMethod or
    this instanceof XmlAttrSetGetMethod or
    // The current URL in a browser may be untrusted or uncontrolled.
    this instanceof WebViewGetUrlMethod
  }
}

private
class EnvTaintedMethod extends Method {
  EnvTaintedMethod() {
    this instanceof MethodSystemGetenv or
    this instanceof PropertiesGetPropertyMethod or
    this instanceof MethodSystemGetProperty
  }
}

class TypeInetAddr extends RefType {
  TypeInetAddr() {
    this.getQualifiedName() = "java.net.InetAddress"
  }
}

class ReverseDNSMethod extends Method {
  ReverseDNSMethod() {
    this.getDeclaringType() instanceof TypeInetAddr and
    (
      this.getName() = "getHostName" or
      this.getName() = "getCanonicalHostName"
    )
  }
}

/** Android `Intent` that may have come from a hostile application. */
class AndroidIntentInput extends DataFlow::Node {
  AndroidIntentInput() {
    exists(MethodAccess ma, AndroidGetIntentMethod m | ma.getMethod().overrides*(m) and
      this.asExpr() = ma
    ) or
    exists(Method m, AndroidReceiveIntentMethod rI | m.overrides*(rI) and
      this.asParameter() = m.getParameter(1)
    )
  }
}
