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
 * Provides classes for modelling common HTTP concepts.
 */

import javascript
import semmle.javascript.frameworks.Express
import semmle.javascript.frameworks.NodeJSLib

module HTTP {
  /**
   * A function invocation that causes a redirect response to be sent.
   */
  abstract class RedirectInvocation extends InvokeExpr {
    /** Gets the argument specifying the URL to redirect to. */
    abstract Expr getUrlArgument();
  }

  /**
   * An expression that sets HTTP response headers.
   */
  abstract class HeaderDefinition extends Expr {
    /**
     * Gets the name of a header set by this definition.
     */
    abstract string getAHeaderName();

    /**
     * Holds if the header named `headerName` is set to `headerValue`.
     */
    abstract predicate defines(string headerName, string headerValue);
  }


  /**
   * An expression that sets HTTP response headers implicitly.
   */
  abstract class ImplicitHeaderDefinition extends HeaderDefinition {

    override string getAHeaderName() {
      defines(result, _)
    }
  }

  /**
   * An expression that sets HTTP response headers explicitly.
   */
  abstract class ExplicitHeaderDefinition extends HeaderDefinition {

    override string getAHeaderName() {
      definesExplicitly(result, _)
    }

    override predicate defines(string headerName, string headerValue) {
      exists(Expr e |
        definesExplicitly(headerName, e) and
        headerValue = e.getStringValue()
      )
    }

    /**
     * Holds if the header named `headerName` is set to the value of `headerValue`.
     */
    abstract predicate definesExplicitly(string headerName, Expr headerValue);
  }

  /**
   * The name of an HTTP request method, in all-uppercase.
   */
  class RequestMethodName extends string {
    RequestMethodName() {
      this = "CHECKOUT" or
      this = "COPY" or
      this = "DELETE" or
      this = "GET" or
      this = "HEAD" or
      this = "LOCK" or
      this = "MERGE" or
      this = "MKACTIVITY" or
      this = "MKCOL" or
      this = "MOVE" or
      this = "M-SEARCH" or
      this = "NOTIFY" or
      this = "OPTIONS" or
      this = "PATCH" or
      this = "POST" or
      this = "PURGE" or
      this = "PUT" or
      this = "REPORT" or
      this = "SEARCH" or
      this = "SUBSCRIBE" or
      this = "TRACE" or
      this = "UNLOCK" or
      this = "UNSUBSCRIBE"
    }
  }

  /**
   * An expression whose value is sent as (part of) the body of an HTTP response.
   */
  abstract class ResponseBody extends Expr {
  }

  /**
   * An expression that sets a cookie in an HTTP response.
   */
  abstract class CookieDefinition extends Expr {
    /**
     * Gets the argument, if any, specifying the raw cookie header.
     */
    Expr getHeaderArgument() { none() }

    /**
     * Gets the argument, if any, specifying the cookie name.
     */
    Expr getNameArgument() { none() }

    /**
     * Gets the argument, if any, specifying the cookie value.
     */
    Expr getValueArgument() { none() }
  }

  /**
   * An expression that sets the `Set-Cookie` header of an HTTP response.
   */
  class SetCookieHeader extends CookieDefinition {
    SetCookieHeader() {
      this.(HeaderDefinition).getAHeaderName() = "Set-Cookie"
    }

    override Expr getHeaderArgument() {
      this.(ExplicitHeaderDefinition).definesExplicitly("Set-Cookie", result)
    }
  }

  /**
   * A server, identified by its creation site.
   */
  abstract class Server extends Expr {
    /**
     * Gets a route handlers of the server.
     */
    abstract RouteHandler getARouteHandler();
  }

  /**
   * A callback for handling a request on some route on a server.
   */
  abstract class RouteHandler extends DataFlowNode {
    /**
     * Gets a header this handler sets.
     */
    abstract HeaderDefinition getAResponseHeader(string name);
  }

}
