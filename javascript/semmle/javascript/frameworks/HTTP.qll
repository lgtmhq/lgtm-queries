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
     * Holds if the header named `headerName` is set to the result of `headerValue`.
     */
    abstract predicate defines(string headerName, Expr headerValue);
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
}