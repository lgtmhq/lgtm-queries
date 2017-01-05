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

/**
 * A JAX WS endpoint is constructed by the container, and its methods
 * are -- where annotated -- called remotely.
 */
class JaxWsEndpoint extends Class {
  JaxWsEndpoint() {
    exists(AnnotationType a | a = this.getAnAnnotation().getType() |
      a.hasName("WebService") or
      a.hasName("WebServiceProvider") or
      a.hasName("WebServiceClient")
    )
  }
  
  Callable getARemoteMethod() {
    result = this.getACallable() and (
      exists(AnnotationType a | a = result.getAnAnnotation().getType() |
        a.hasName("WebMethod") or
        a.hasName("WebEndpoint")
      )
    )
  }
}

/**
 * A JAX RS service. Annotated methods are reflectively called by the container. The
 * class itself may be reflectively constructed by the container.
 */
class JaxRsService extends Class {
  JaxRsService() {
    exists(AnnotationType a |
      a = this.getAnAnnotation().getType() and
      a.getPackage().getName() = "javax.ws.rs" |
      a.hasName("Path")
    )
  }

  Callable getARemoteMethod() {
    result = this.getACallable() and (
      exists(AnnotationType a |
        a = result.getAnAnnotation().getType() and
        a.getPackage().getName() = "javax.ws.rs" |
        a.hasName("GET") or
        a.hasName("POST") or
        a.hasName("DELETE") or
        a.hasName("PUT") or 
        a.hasName("OPTIONS") or
        a.hasName("HEAD")
      )
    )
  }
}

class JaxRsResponse extends Class {
  JaxRsResponse() {
    this.hasQualifiedName("javax.ws.rs.core", "Response")
  }
}

class JaxRsResponseBuilder extends Class {
  JaxRsResponseBuilder() {
    this.hasQualifiedName("javax.ws.rs.core", "ResponseBuilder")
  }
}
