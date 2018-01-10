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
 * Provides classes and predicates for working with the Java Servlet API.
 */

import semmle.code.java.Type

/**
 * The interface `javax.servlet.ServletRequest` or
 * `javax.servlet.http.HttpServletRequest`.
 */
library
class ServletRequest extends RefType {
  ServletRequest() {
    hasQualifiedName("javax.servlet", "ServletRequest") or
    this instanceof HttpServletRequest
  }
}

/**
 * The interface `javax.servlet.http.HttpServletRequest`.
 */
library
class HttpServletRequest extends RefType {
  HttpServletRequest() {
    hasQualifiedName("javax.servlet.http", "HttpServletRequest")
  }
}

/**
 * The method `getParameter(String)` or `getParameterValues(String)`
 * declared in `javax.servlet.ServletRequest`.
 */
library
class ServletRequestGetParameterMethod extends Method {
  ServletRequestGetParameterMethod() {
    getDeclaringType() instanceof ServletRequest and
    (
      hasName("getParameter")  or
      hasName("getParameterValues")
    ) and
    getNumberOfParameters() = 1 and
    getParameter(0).getType() instanceof TypeString
  }
}

/**
 * The method `getQueryString()` declared in `javax.servlet.http.HttpServletRequest`.
 */
library
class HttpServletRequestGetQueryStringMethod extends Method {
  HttpServletRequestGetQueryStringMethod() {
    getDeclaringType() instanceof HttpServletRequest and
    hasName("getQueryString") and
    getNumberOfParameters() = 0
  }
}

/**
 * The method `getPathInfo()` declared in `javax.servlet.http.HttpServletRequest`.
 */
library
class HttpServletRequestGetPathMethod extends Method {
  HttpServletRequestGetPathMethod() {
    getDeclaringType() instanceof HttpServletRequest and
    hasName("getPathInfo") and
    getNumberOfParameters() = 0
  }
}

/**
 * The method `getHeader(String)` declared in `javax.servlet.http.HttpServletRequest`.
 */
library
class HttpServletRequestGetHeaderMethod extends Method {
  HttpServletRequestGetHeaderMethod() {
    getDeclaringType() instanceof HttpServletRequest and
    hasName("getHeader") and
    getNumberOfParameters() = 1 and
    getParameter(0).getType() instanceof TypeString
  }
}

/**
 * The method `getInputStream()` or `getReader()` declared in `javax.servlet.ServletRequest`.
 */
library
class ServletRequestGetBodyMethod extends Method {
  ServletRequestGetBodyMethod() {
    getDeclaringType() instanceof ServletRequest and
    (hasName("getInputStream") or hasName("getReader"))
  }
}

/**
 * The interface `javax.servlet.ServletResponse` or
 * `javax.servlet.http.HttpServletResponse`.
 */
class ServletResponse extends RefType {
  ServletResponse() {
    hasQualifiedName("javax.servlet", "ServletResponse") or
    this instanceof HttpServletResponse
  }
}

/**
 * The interface `javax.servlet.http.HttpServletResponse`.
 */
class HttpServletResponse extends RefType {
  HttpServletResponse() {
    hasQualifiedName("javax.servlet.http", "HttpServletResponse")
  }
}

/**
 * The method `sendError(int,String)` declared in `javax.servlet.http.HttpServletResponse`.
 */
class HttpServletResponseSendErrorMethod extends Method {
  HttpServletResponseSendErrorMethod() {
    getDeclaringType() instanceof HttpServletResponse and
    hasName("sendError") and
    getNumberOfParameters() = 2 and
    getParameter(0).getType().hasName("int") and
    getParameter(1).getType() instanceof TypeString
  }
}

/**
 * The method `sendRedirect(String)` declared in `javax.servlet.http.HttpServletResponse`.
 */
class HttpServletResponseSendRedirectMethod extends Method {
  HttpServletResponseSendRedirectMethod() {
    getDeclaringType() instanceof HttpServletResponse and
    hasName("sendRedirect") and
    getNumberOfParameters() = 1 and
    getParameter(0).getType() instanceof TypeString
  }
}

/**
 * The method `getWriter()` declared in `javax.servlet.ServletResponse`.
 */
class ServletResponseGetWriterMethod extends Method {
  ServletResponseGetWriterMethod() {
    getDeclaringType() instanceof ServletResponse and
    hasName("getWriter") and
    getNumberOfParameters() = 0
  }
}

/**
 * The method `getOutputStream()` declared in `javax.servlet.ServletResponse`.
 */
class ServletResponseGetOutputStreamMethod extends Method {
  ServletResponseGetOutputStreamMethod() {
    getDeclaringType() instanceof ServletResponse and
    hasName("getOutputStream") and
    getNumberOfParameters() = 0
  }
}

/** The class `javax.servlet.http.Cookie`. */
library
class TypeCookie extends Class {
  TypeCookie() {
    hasQualifiedName("javax.servlet.http", "Cookie")
  }
}

/**
 * The method `getValue(String)` declared in `javax.servlet.http.Cookie`.
 */
library
class CookieGetValueMethod extends Method {
  CookieGetValueMethod() {
    getDeclaringType() instanceof TypeCookie and
    hasName("getValue") and
    getReturnType() instanceof TypeString
  }
}

/**
 * The method `addCookie(String)` declared in `javax.servlet.http.Cookie`.
 */
class ResponseAddCookieMethod extends Method {
  ResponseAddCookieMethod() {
    getDeclaringType() instanceof HttpServletResponse and
    hasName("addCookie")
  }
}

/**
 * The method `addHeader` declared in `javax.servlet.http.HttpServletResponse`.
 */
class ResponseAddHeaderMethod extends Method {
  ResponseAddHeaderMethod() {
    getDeclaringType() instanceof HttpServletResponse and
    hasName("addHeader")
  }
}

/**
 * The method `setHeader` declared in `javax.servlet.http.HttpServletResponse`.
 */
class ResponseSetHeaderMethod extends Method {
  ResponseSetHeaderMethod() {
    getDeclaringType() instanceof HttpServletResponse and
    hasName("setHeader")
  }
}

/**
 * A class that has `javax.servlet.Servlet` as an ancestor.
 */
class ServletClass extends Class {
  ServletClass() {
    getAnAncestor().hasQualifiedName("javax.servlet", "Servlet")
  }
}

/**
 * The set of `Servlet` listener types that can be specified in a `web.xml` file.
 *
 * Note: There are a number of other listener interfaces in the `javax.servlet` package that cannot
 * be configured in `web.xml` and therefore are not covered by this class.
 */
class ServletWebXMLListenerType extends RefType {
  ServletWebXMLListenerType() {
    hasQualifiedName("javax.servlet", "ServletContextAttributeListener") or
    hasQualifiedName("javax.servlet", "ServletContextListener") or
    hasQualifiedName("javax.servlet", "ServletRequestAttributeListener") or
    hasQualifiedName("javax.servlet", "ServletRequestListener") or
    hasQualifiedName("javax.servlet.http", "HttpSessionAttributeListener") or
    hasQualifiedName("javax.servlet.http", "HttpSessionIdListener") or
    hasQualifiedName("javax.servlet.http", "HttpSessionListener")
    /*
     * Listeners that are not configured in `web.xml`:
     *  - `HttpSessionActivationListener`
     *  - `HttpSessionBindingListener`
     */
  }
}
