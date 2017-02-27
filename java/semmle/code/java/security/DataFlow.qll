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
 * Data flow module in the security pack.
 *
 * This module tracks data through a program.
 */

import semmle.code.java.Expr
import semmle.code.java.frameworks.Jdbc
import semmle.code.java.frameworks.Networking
import semmle.code.java.frameworks.Properties
import semmle.code.java.frameworks.Rmi
import semmle.code.java.frameworks.Servlets
import semmle.code.java.frameworks.ApacheHttp
import semmle.code.java.frameworks.android.XmlParsing
import semmle.code.java.frameworks.android.WebView
import semmle.code.java.frameworks.android.SQLite
import semmle.code.java.frameworks.JaxWS
import semmle.code.java.dataflow.DefUse
import semmle.code.java.security.SecurityTests
import semmle.code.java.security.Validation
import semmle.code.java.dispatch.VirtualDispatch

/** Class representing a source of data flow. */
class FlowSource extends Expr {
  /** Whether this source flows to the `sink`. */
  predicate flowsTo(Expr sink) {
    flowsToAndLocal((FlowExpr) sink)
  }

  /**
   * The same as `flowsTo(sink,fromArg)`, plus `localFlow` and reads from instance fields.
   * This gives us a little bit of flow through instance fields, without
   * letting it escape back out of the class.
   */
  private predicate flowsToAndLocal(FlowExpr sink) {
    // Verify that the sink is not excluded for this `FlowSource`.
    not isExcluded(sink) and
    (
      flowsTo(sink, _) or
      exists (FlowExpr tracked |
        // The tracked expression should not be excluded for this `FlowSource`.
        not isExcluded(tracked) and
        flowsToAndLocal(tracked) and (
          localFlowStep(tracked, sink) or
          exists (Field field |
            tracked = field.getAnAssignedValue() and
            sink = field.getAnAccess()
          )
        )
      )
    )
  }

  /**
   * Sinks that this flow source flows to. The `fromArg` column is
   * `true` if the `sink` is in a method where one of the arguments
   * holds the same value as `sink`.
   */
  private predicate flowsTo(FlowExpr sink, boolean fromArg) {
    // Base case.
    sink = this and fromArg = false

    or exists(FlowExpr tracked |
      // The tracked expression should not be excluded for this `FlowSource`.
      not isExcluded(tracked) |
      // Flow within a single method.
      (flowsTo(tracked, fromArg) and
        localFlowStep(tracked, sink)
      )
      // Flow through a field.
      or (flowsTo(tracked, _) and
        staticFieldStep(tracked, sink) and
        fromArg = false
      )
      // Flow through a method that returns one of its arguments.
      or exists(MethodAccess call, int i |
        flowsTo(tracked, fromArg) and
        methodReturnsArg(responderForArg(call, i, tracked), i) and
        sink = call
      )
      // Flow into a method.
      or exists(Call c, Callable m, Parameter p, int i |
        flowsTo(tracked, _) and
        m = responderForArg(c, i, tracked) and
        m.getParameter(i) = p and
        exists(UseStmt u | parameterUse(p, u) and sink = u.getAUse(p)) and
        fromArg = true
      )
      // Flow out of a method.
      // This path is only enabled if the flow did not come from the argument;
      // such cases are handled by `methodReturnsArg`.
      or (
        flowsTo(tracked, false) and
        methodStep(tracked, sink) and
        fromArg = false
      )
    )
  }

  /**
   * A version of `flowsTo` that searches backwards from the `sink` instead of
   * forwards from the source. This does not include flow paths across methods.
   */
  predicate flowsToReverse(Expr sink) {
    sink instanceof FlowExpr and
    // The tracked expression should not be excluded for this `FlowSource`.
    not isExcluded(sink.(FlowExpr)) and
    (
      sink = this
      or exists(FlowSource tracked | tracked.flowsToReverse(sink) |
        localFlowStep(this, tracked)
      )
      or exists(FlowSource tracked | tracked.flowsToReverse(sink) |
        staticFieldStep(this, tracked)
      )
      or exists(FlowSource tracked, MethodAccess call, int i |
        tracked.flowsToReverse(sink) and
        tracked = call and
        methodReturnsArg(call.getMethod(), i) and
        call.getArgument(i) = this
      )
    )
  }

  /**
   * Flow expressions that should be excluded by the flow analysis for this type of `FlowSource`.
   */
  predicate isExcluded(FlowExpr flowExpr) {
    // Nothing excluded by default
    none()
  }
}

/**
 * Expressions that are considered valid for flow.
 * This should be private.
 */
class FlowExpr extends Expr {
  FlowExpr() {
    // Ignore paths through test code.
    not getEnclosingCallable().getDeclaringType() instanceof NonSecurityTestClass and

    not exists (ValidatedVariable var | this = var.getAnAccess())
  }
}

/** The responders for a `call` with given argument. */
pragma[nomagic]
private Callable responderForArg(Call call, int i, FlowExpr tracked) {
  call.getArgument(i) = tracked and
  result = responder(call)
}

/** The responders to consider when tracking flow through a `call`. */
private Callable responder(Call call) {
  result = exactCallable(call) or
  (
    not exists(exactCallable(call)) and
    result = call.getCallee()
  )
}

/** Whether a method can return its argument. This is public for testing. */
predicate methodReturnsArg(Method method, int arg) {
  exists (ReturnStmt ret |
    ret.getEnclosingCallable() = method and
    ret.getResult() = parameterFlow(method, arg)
  )
}

/**
 * The local flow of a parameter, including flow through other methods
 * that return their argument.
 */
private Expr parameterFlow(Method method, int arg) {
  result = method.getParameter(arg).getAnAccess() or
  exists (Expr tracked | tracked = parameterFlow(method, arg) |
    localFlowStep(tracked, result) or
    exists (MethodAccess acc, int j |
      acc.getArgument(j) = tracked and
      methodReturnsArg(acc.getMethod(), j) and
      result = acc
    )
  )
}

/**
 * One step of flow within a single method.
 */
cached private predicate localFlowStep(Expr tracked, Expr sink) {
  variableStep(tracked, sink)

  // A concatenation of a tracked expression.
  or sink.(AddExpr).getAnOperand() = tracked

  // A parenthesized tracked expression.
  or sink.(ParExpr).getExpr() = tracked

  // A cast of a tracked expression.
  or sink.(CastExpr).getExpr() = tracked

  // A conditional expression with a tracked branch.
  or sink.(ConditionalExpr).getTrueExpr() = tracked
  or sink.(ConditionalExpr).getFalseExpr() = tracked

  // An array initialization or creation expression.
  or sink.(ArrayCreationExpr).getInit() = tracked
  or sink.(ArrayInit).getAnInit() = tracked

  // An access to an element of a tracked array.
  or sink.(ArrayAccess).getArray() = tracked

  or arrayAccessStep(tracked, sink)

  or constructorStep(tracked, sink)

  or qualifierToMethodStep(tracked, sink)

  or argToMethodStep(tracked, sink)

  // An unsafe attempt to escape tainted input.
  or (unsafeEscape(sink) and sink.(MethodAccess).getQualifier() = tracked)

  // A logic expression.
  or sink.(LogicExpr).getAnOperand() = tracked

  or comparisonStep(tracked, sink)

  or stringBuilderStep(tracked, sink)

  or serializationStep(tracked, sink)
}

/** A use of a variable that has been assigned a `tracked` expression. */
private predicate variableStep(Expr tracked, VarAccess sink) {
  exists(Variable v, DefStmt def, UseStmt use |
    def.getADef(v).getSource() = tracked and
    use.getAUse(v) = sink and
    defUsePair(v, def, use)
  )
}

private predicate staticFieldStep(Expr tracked, FieldAccess sink) {
  exists(Field f |
    f.isStatic() and
    f.getAnAssignedValue() = tracked | f.getAnAccess() = sink
  )
}

/** An access to an array that has been assigned a `tracked` element. */
private predicate arrayAccessStep(Expr tracked, Expr sink) {
  exists(Assignment assign | assign.getSource() = tracked |
    sink = assign.getDest().(ArrayAccess).getArray().(VarAccess).getVariable().getAnAccess()
  )
}

/** An access to a method that returns a `tracked` expression. */
private predicate methodStep(Expr tracked, MethodAccess sink) {
  exists(Method m, ReturnStmt ret | ret.getResult() = tracked and ret.getEnclosingCallable() = m |
    m = responder(sink)
  )
}
/** Access to a method that passes taint from an argument. */
private predicate argToMethodStep(Expr tracked, MethodAccess sink) {
  exists(Method m, int i |
    m = ((MethodAccess) sink).getMethod()
    and dataPreservingArgument(m, i)
    and tracked = ((MethodAccess) sink).getArgument(i)
  )
}

/** A comparison or equality test with a constant. */
private predicate comparisonStep(Expr tracked, Expr sink) {
  exists(Expr other |
    (
      exists(BinaryExpr e | e instanceof ComparisonExpr or e instanceof EqualityTest |
        e = sink
        and e.getAnOperand() = tracked
        and e.getAnOperand() = other
      )
      or
      exists(MethodAccess m | m.getMethod() instanceof EqualsMethod |
        m = sink
        and (
          (m.getQualifier() = tracked and m.getArgument(0) = other) or
          (m.getQualifier() = other and m.getArgument(0) = tracked)
        )
      )
    )
    and (other.isCompileTimeConstant() or other instanceof NullLiteral)
    and tracked != other
  )
}

/** Flow through a `StringBuilder`. */
private predicate stringBuilderStep(Expr tracked, Expr sink) {
  exists(StringBuilderVar sbvar |
    exists(MethodAccess input, int arg |
      input = sbvar.getAnInput(arg) and
      tracked = input.getArgument(arg)
    )
    and sink = sbvar.getToStringCall()
  )
}

/** Flow through data serialization. */
private predicate serializationStep(Expr tracked, Expr sink) {
  exists(ObjectOutputStreamVar v, DefStmt def |
    def = v.getADefStmt() and
    exists(MethodAccess ma, UseStmt use |
      ma.getArgument(0) = tracked and
      ma = v.getAWriteObjectMethodAccess() and
      use = ma.getEnclosingStmt() and
      defUsePair(v, def, use)
    ) and
    exists(LocalVariableDecl v2, UseStmt use, ClassInstanceExpr cie |
      cie = def.getADef(v).getSource() and
      v2 = cie.getArgument(0).(RValue).getVariable() and
      useUsePair(v2, def, use) and
      use.getAUse(v2) = sink
    )
  )
}

/**
 * A local variable that is assigned an `ObjectOutputStream`.
 * Writing tainted data to such a stream causes the underlying
 * `OutputStream` to be tainted.
 */
class ObjectOutputStreamVar extends LocalVariableDecl {
  ObjectOutputStreamVar() {
    exists(ClassInstanceExpr cie | cie = this.getAnAssignedValue() |
      cie.getType() instanceof TypeObjectOutputStream
    )
  }

  DefStmt getADefStmt() {
    definition(this, result) and
    result.getADef(this).getSource().(ClassInstanceExpr).getType() instanceof TypeObjectOutputStream
  }

  MethodAccess getAWriteObjectMethodAccess() {
    result.getQualifier() = getAnAccess() and
    result.getMethod().hasName("writeObject")
  }
}

/**
 * A local variable that is initialized to a `StringBuilder`
 * or `StringBuffer`. Such variables are often used to
 * build up a query using string concatenation.
 */
class StringBuilderVar extends LocalVariableDecl {
  StringBuilderVar() {
    this.getType() instanceof TypeStringBuilder or
    this.getType() instanceof TypeStringBuffer
  }

  /**
   * A call that adds something to this string builder, from the argument at the given index.
   */
  MethodAccess getAnInput(int arg) {
    result.getQualifier() = getAChainedReference()
    and
    (
      result.getMethod().getName() = "append" and arg = 0
      or result.getMethod().getName() = "insert" and arg = 1
      or result.getMethod().getName() = "replace" and arg = 2
    )
  }

  /**
   * A call that appends something to this string builder.
   */
  MethodAccess getAnAppend() {
    result.getQualifier() = getAChainedReference()
    and result.getMethod().getName() = "append"
  }

  /**
   * A call that converts this string builder to a string.
   */
  MethodAccess getToStringCall() {
    result.getQualifier() = getAChainedReference()
    and result.getMethod().getName() = "toString"
  }

  /**
   * An expression that refers to this `StringBuilder`, possibly after some chained calls.
   */
  Expr getAChainedReference() {
    // All the methods on `StringBuilder` that return the same type return
    // the same object.
    result = callReturningSameType+(this.getAnAccess())
    or
    result = this.getAnAccess()
  }
}

private MethodAccess callReturningSameType(Expr ref) {
  ref = result.getQualifier() and
  result.getMethod().getReturnType() = ref.getType()
}

private class BulkData extends RefType {
  BulkData() {
    this.(Array).getElementType().(PrimitiveType).getName().regexpMatch("byte|char") or
    exists(RefType t | this.getASourceSupertype*() = t |
      t.hasQualifiedName("java.io", "InputStream") or
      t.hasQualifiedName("java.nio", "ByteBuffer") or
      t.hasQualifiedName("java.lang", "Readable") or
      t.hasQualifiedName("java.io", "DataInput") or
      t.hasQualifiedName("java.nio.channels", "ReadableByteChannel")
    )
  }
}

/**
 * Holds if `c` is a constructor for a subclass of `java.io.InputStream` that
 * wraps an underlying data source. The underlying data source is given as a
 * the `argi`'th parameter to the constructor.
 *
 * An object construction of such a wrapper is likely to preserve the data flow
 * status of its argument.
 */
private predicate inputStreamWrapper(Constructor c, int argi) {
  c.getParameterType(argi) instanceof BulkData and
  c.getDeclaringType().getASourceSupertype().hasQualifiedName("java.io", "InputStream")
}

/** An object construction that preserves the data flow status of any of its arguments. */
predicate constructorStep(Expr tracked, ConstructorCall sink) {
  exists(int argi | sink.getArgument(argi) = tracked |
    exists(string s | sink.getConstructedType().getQualifiedName() = s |
      // String constructor does nothing to data
      s = "java.lang.String" and argi = 0 or
      // some readers preserve the content of streams
      s = "java.io.InputStreamReader" and argi = 0  or
      s = "java.io.BufferedReader" and argi = 0  or
      s = "java.io.CharArrayReader" and argi = 0  or
      s = "java.io.StringReader" and argi = 0  or
      // data preserved through streams
      s = "java.io.ObjectInputStream" and argi = 0  or
      s = "java.io.ByteArrayInputStream" and argi = 0  or
      s = "java.io.DataInputStream" and argi = 0  or
      s = "java.io.BufferedInputStream" and argi = 0  or
      s = "com.esotericsoftware.kryo.io.Input" and argi = 0  or
      s = "java.beans.XMLDecoder" and argi = 0  or
      // a tokenizer preserves the content of a string
      s = "java.util.StringTokenizer" and argi = 0  or
      // unzipping the stream preserves content
      s = "java.util.zip.ZipInputStream" and argi = 0  or
      s = "java.util.zip.GZIPInputStream" and argi = 0  or
      // string builders and buffers
      s = "java.lang.StringBuilder" and argi = 0  or
      s = "java.lang.StringBuffer" and argi = 0  or
      // a cookie with tainted ingredients is tainted
      s = "javax.servlet.http.Cookie" and argi = 0 or
      s = "javax.servlet.http.Cookie" and argi = 1
    ) or
    exists(RefType t | t.getQualifiedName() = "java.lang.Number" |
      hasSubtypeStar(t, sink.getConstructedType())
    ) and argi = 0 or
    // wrappers constructed by extension
    exists(Constructor c, Parameter p, SuperConstructorInvocationStmt sup |
      c = sink.getConstructor() and
      p = c.getParameter(argi) and
      sup.getEnclosingCallable() = c and
      constructorStep(p.getAnAccess(), sup)
    ) or
    // a custom InputStream that wraps a tainted data source is tainted
    inputStreamWrapper(sink.getConstructor(), argi)
  )
}

/** Access to a method that passes taint from the qualifier. */
predicate qualifierToMethodStep(Expr tracked, MethodAccess sink) {
  sink.getMethod() instanceof DataPreservingMethod and
  tracked = sink.getQualifier()
}

/**
 * Methods that return tainted data when called on tainted data.
 */
class DataPreservingMethod extends Method {
  DataPreservingMethod() {
    (
      this.getDeclaringType() instanceof TypeString and
      (
        this.getName() = "endsWith" or
        this.getName() = "getBytes" or
        this.getName() = "split" or
        this.getName() = "substring" or
        this.getName() = "toCharArray" or
        this.getName() = "toLowerCase" or
        this.getName() = "toString" or
        this.getName() = "toUpperCase" or
        this.getName() = "trim"
      )
    ) or
    (
      exists(Class c | c.getQualifiedName() = "java.lang.Number" |
      hasSubtypeStar(c, this.getDeclaringType())) and
      (
        this.getName().matches("to%String") or
        this.getName() = "toByteArray" or
        this.getName().matches("%Value")
      )
    ) or
    (
      this.getDeclaringType().getQualifiedName().matches("%Reader") and
      this.getName().matches("read%")
    ) or
    (
      this.getDeclaringType().getQualifiedName().matches("StringWriter") and
      this.getName() = "toString"
    ) or
    (
      this.getDeclaringType().hasQualifiedName("java.util", "StringTokenizer") and
      this.getName().matches("next%")
    ) or
    (
      this.getDeclaringType().hasQualifiedName("java.io", "ByteArrayOutputStream") and
      (this.getName() = "toByteArray" or this.getName() = "toString")
    ) or
    (
      this.getDeclaringType().hasQualifiedName("java.io", "ObjectInputStream") and
      this.getName().matches("read%")
    ) or
    (
      (
        this.getDeclaringType().hasQualifiedName("java.lang", "StringBuilder") or
        this.getDeclaringType().hasQualifiedName("java.lang", "StringBuffer")
      ) and
      (
        this.getName() = "toString" or this.getName() = "append"
      )
    )
  }
}

/**
 * Library methods that return tainted data if one of their arguments
 * is tainted.
 */
predicate dataPreservingArgument(Method method, int arg) {
  (
    method instanceof StringReplaceMethod and
    arg = 1
  ) or
  (
    exists(Class c | c.getQualifiedName() = "java.lang.Number" |
      hasSubtypeStar(c, method.getDeclaringType())
    ) and
    (
      (method.getName().matches("parse%") and arg = 0) or
      (method.getName().matches("valueOf%") and arg = 0) or
      (method.getName().matches("to%String") and arg = 0)
    )
  ) or
  (
    (
      method.getDeclaringType().hasQualifiedName("java.lang", "StringBuilder") or
      method.getDeclaringType().hasQualifiedName("java.lang", "StringBuffer")
    ) and
    (
      method.getName() = "append" and arg = 0
      or
      method.getName() = "insert" and arg = 1
      or
      method.getName() = "replace" and arg = 2
    )
  ) or
  (
    (
      method.getDeclaringType().hasQualifiedName("java.util", "Base64$Encoder") or
      method.getDeclaringType().hasQualifiedName("java.util", "Base64$Decoder")
    ) and
    (
      method.getName() = "encode" and arg = 0 and method.getNumberOfParameters() = 1 or
      method.getName() = "decode" and arg = 0 and method.getNumberOfParameters() = 1 or
      method.getName() = "encodeToString" and arg = 0 or
      method.getName() = "wrap" and arg = 0
    )
  )
}

class StringReplaceMethod extends Method {
  StringReplaceMethod() {
    getDeclaringType() instanceof TypeString and
    (
      hasName("replace") or
      hasName("replaceAll") or
      hasName("replaceFirst")
    )
  }
}

predicate unsafeEscape(MethodAccess ma) {
  // Removing `<script>` tags using a string-replace method is
  // unsafe if such a tag is embedded inside another one (e.g. `<scr<script>ipt>`).
  exists(StringReplaceMethod m | ma.getMethod() = m |
    ma.getArgument(0).(StringLiteral).getRepresentedString() = "(<script>)" and
    ma.getArgument(1).(StringLiteral).getRepresentedString() = ""
  )
}

/** Class for `tainted` user input. */
abstract class UserInput extends FlowSource {}

/** Input that may be controlled by a remote user. */
class RemoteUserInput extends UserInput {
  RemoteUserInput() {
    this.(MethodAccess).getMethod() instanceof RemoteTaintedMethod

    // Parameters to RMI methods.
    or exists (RemoteCallableMethod method |
       method.getAParameter().getAnAccess() = this
       and (
         getType() instanceof PrimitiveType
         or getType() instanceof TypeString
       )
    )

    // Parameters to Jax WS methods.
    or exists (JaxWsEndpoint endpoint |
       endpoint.getARemoteMethod().getAParameter().getAnAccess() = this
    )
    // Parameters to Jax Rs methods.
    or exists (JaxRsResourceClass service |
       service.getAnInjectableCallable().getAParameter().getAnAccess() = this or
       service.getAnInjectableField().getAnAccess() = this
    )

    // Reverse DNS. Try not to trigger on `localhost`.
    or exists(MethodAccess m | m = this |
      m.getMethod() instanceof ReverseDNSMethod and
      not exists(MethodAccess l |
        (variableStep(l, m.getQualifier()) or l = m.getQualifier())
        and l.getMethod().getName() = "getLocalHost"
      )
    )
  }
}

/** Input that may be controlled by a local user. */
abstract class LocalUserInput extends UserInput {}

class EnvInput extends LocalUserInput {
  EnvInput() {
    // Parameters to a main method.
    exists (MainMethod main | this = main.getParameter(0).getAnAccess())

    // Args4j arguments.
    or exists (Field f | this = f.getAnAccess() | f.getAnAnnotation().getType().getQualifiedName() = "org.kohsuke.args4j.Argument")

    // Results from various specific methods.
    or this.(MethodAccess).getMethod() instanceof EnvTaintedMethod

    // Access to `System.in`.
    or exists(Field f | this = f.getAnAccess() | f instanceof SystemIn)

    // Access to files.
    or this.(ConstructorCall).getConstructedType().hasQualifiedName("java.io", "FileInputStream")
  }
}

class DatabaseInput extends LocalUserInput {
  DatabaseInput() {
    this.(MethodAccess).getMethod() instanceof ResultSetGetStringMethod
  }
}

library
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

library
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
