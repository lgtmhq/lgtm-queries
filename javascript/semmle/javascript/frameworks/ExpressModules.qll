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
 * Models of npm modules that are used with Express servers.
 */
import javascript
import semmle.javascript.frameworks.HTTP

module ExpressLibraries {

  /**
  * Holds if `headerName` and `headerValue` corresponds to a default "X-Frame-Options" HTTP header.
  */
  private predicate xFrameOptionsDefaultImplicitHeaderDefinition(string headerName, string headerValue) {
    headerName = "X-Frame-Options" and headerValue = "DENY"
  }

  /**
   * Header produced by a route handler of the "x-frame-options" module.
   */
  class XFrameOptionsRouteHandlerHeader extends HTTP::ImplicitHeaderDefinition {

    XFrameOptionsRouteHandlerHeader() {
      this instanceof XFrameOptionsRouteHandler
    }

    override predicate defines(string headerName, string headerValue) {
      xFrameOptionsDefaultImplicitHeaderDefinition(headerName, headerValue)
    }

    override HTTP::RouteHandler getRouteHandler() {
      result = this
    }
  }

  /**
   * Route handler from the "x-frame-options" module.
   */
  class XFrameOptionsRouteHandler extends HTTP::RouteHandler {
    XFrameOptionsRouteHandler() {
      this = DataFlow::moduleImport("x-frame-options").getAnInvocation()
    }

    override HTTP::HeaderDefinition getAResponseHeader(string name) {
      name = this.(XFrameOptionsRouteHandlerHeader).getAHeaderName() and
      result = this
    }

  }


  /**
   * Header produced by a route handler of the "frameguard" module.
   */
  class FrameGuardRouteHandlerHeader extends HTTP::ImplicitHeaderDefinition {

    FrameGuardRouteHandlerHeader() {
      this instanceof FrameGuardRouteHandler
    }

    override predicate defines(string headerName, string headerValue) {
      xFrameOptionsDefaultImplicitHeaderDefinition(headerName, headerValue)
    }

    override HTTP::RouteHandler getRouteHandler() {
      result = this
    }
  }

  /**
   * Route handler from the "frameguard" module.
   */
  class FrameGuardRouteHandler extends HTTP::RouteHandler {
    FrameGuardRouteHandler() {
      this = DataFlow::moduleImport("frameguard").getAnInvocation()
    }

    override HTTP::HeaderDefinition getAResponseHeader(string name) {
      name = this.(FrameGuardRouteHandlerHeader).getAHeaderName() and
      result = this
    }

  }


  /**
   * Header produced by a route handler of the "helmet" module.
   */
  class HelmetRouteHandlerHeader extends HTTP::ImplicitHeaderDefinition {

    HelmetRouteHandlerHeader() {
      this instanceof HelmetRouteHandler
    }

    override predicate defines(string headerName, string headerValue) {
      xFrameOptionsDefaultImplicitHeaderDefinition(headerName, headerValue)
    }

    override HTTP::RouteHandler getRouteHandler() {
      result = this
    }
  }

  /**
   * Route handler from the "helmet" module.
   */
  class HelmetRouteHandler extends HTTP::RouteHandler {
    HelmetRouteHandler() {
      exists (DataFlow::ModuleImportNode m | "helmet" = m.getPath() |
        this = m.getAnInvocation()  or
        this = m.getAMemberInvocation("frameguard")
      )
    }

    override HTTP::HeaderDefinition getAResponseHeader(string name) {
      name = this.(HelmetRouteHandlerHeader).getAHeaderName() and
      result = this
    }

  }

}
