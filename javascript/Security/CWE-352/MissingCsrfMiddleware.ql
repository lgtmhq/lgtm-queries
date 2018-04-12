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

/**
 * @name Missing CSRF middleware
 * @description Using cookies without CSRF protection may allow malicious websites to
 *              submit requests on behalf of the user.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @id js/missing-token-validation
 * @tags security
 *       external/cwe/cwe-352
 */

import javascript

/**
 * Gets an expression that creates a route handler that parses cookies.
 *
 * A router handler following after cookie parsing is assumed to depend on
 * cookies, and thus require CSRF protection.
 */
DataFlow::CallNode cookieMiddlewareCreation() {
  exists (DataFlow::ModuleImportNode mod | result = mod.getACall() |
    mod.getPath() = "cookie-parser" or
    mod.getPath() = "cookie-session" or
    mod.getPath() = "express-session")
}

/**
 * Checks if `expr` is preceded by the cookie middleware `cookie`.
 */
predicate hasCookieMiddleware(Express::RouteHandlerExpr expr, Express::RouteHandlerExpr cookie) {
  cookieMiddlewareCreation().flowsToExpr(cookie) and
  expr.getAMatchingAncestor() = cookie
}

/**
 * Gets an expression that creates a route handler which protects against CSRF attacks.
 *
 * Any route handler registered downstream from this type of route handler will
 * be considered protected.
 *
 * For example:
 * ```
 * let csurf = require('csurf');
 * let csrfProtector = csurf();
 *
 * app.post('/changePassword', csrfProtector, function (req, res) {
 *   // protected from CSRF
 * })
 * ```
 *
 * Currently the predicate only detects `csurf`-based protectors.
 */
DataFlow::CallNode csrfMiddlewareCreation() {
  exists (DataFlow::ModuleImportNode mod | result = mod.getACall() |
    mod.getPath() = "csurf"
  )
}

/**
 * Holds if the given route handler is protected by CSRF middleware.
 */
predicate hasCsrfMiddleware(Express::RouteHandlerExpr handler) {
  csrfMiddlewareCreation().flowsToExpr(handler.getAMatchingAncestor())
}

from Express::RouterDefinition router, Express::RouteSetup setup, Express::RouteHandlerExpr handler,
     Express::RouteHandlerExpr cookie
where router = setup.getRouter()
  and handler = setup.getARouteHandlerExpr()

  and hasCookieMiddleware(handler, cookie)
  and not hasCsrfMiddleware(handler)

  // Only warn for the last handler in a chain.
  and handler.isLastHandler()

  // Only warn for dangerous for handlers, such as for POST and PUT.
  and not setup.getRequestMethod().isSafe()

select cookie, "This cookie middleware is serving a request handler $@ without CSRF protection.", handler, "here"
