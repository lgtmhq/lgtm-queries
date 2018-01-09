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
import semmle.code.java.Serializability
import semmle.code.java.dataflow.DataFlow

/** The method `parseAs` in `com.google.api.client.http.HttpResponse`. */
private class ParseAsMethod extends Method {
  ParseAsMethod() {
    this.getDeclaringType().hasQualifiedName("com.google.api.client.http", "HttpResponse") and
    this.hasName("parseAs")
  }
}

private class TypeLiteralToParseAsFlowConfiguration extends DataFlow::Configuration {
  TypeLiteralToParseAsFlowConfiguration() {
    this = "GoogleHttpClientApi::TypeLiteralToParseAsFlowConfiguration"
  }
  override predicate isSource(DataFlow::Node source) {
    source.asExpr() instanceof TypeLiteral
  }
  override predicate isSink(DataFlow::Node sink) {
    exists(MethodAccess ma |
      ma.getAnArgument() = sink.asExpr() and
      ma.getMethod() instanceof ParseAsMethod
    )
  }
  TypeLiteral getSourceWithFlowToParseAs() {
    hasFlow(DataFlow::exprNode(result), _)
  }
}

/** A field that is deserialized by `HttpResponse.parseAs`. */
class HttpResponseParseAsDeserializableField extends DeserializableField {
  HttpResponseParseAsDeserializableField() {
    exists(RefType decltype, TypeLiteralToParseAsFlowConfiguration conf |
      decltype = getDeclaringType() and
      conf.getSourceWithFlowToParseAs().getTypeName().getType() = decltype and
      decltype.fromSource()
    )
  }
}
