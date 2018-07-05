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

/**
 * Holds if any `web.xml` files are included in this snapshot.
 */
predicate isWebXMLIncluded() {
  exists(WebXMLFile webXML)
}

/**
 * A deployment descriptor file, typically called `web.xml`.
 */
class WebXMLFile extends XMLFile {
  WebXMLFile() {
    count(XMLElement e | e = this.getAChild()) = 1 and
    this.getAChild().getName() = "web-app"
  }

  /**
   * Gets the value of the context parameter with the given name.
   */
  string getContextParamValue(string name) {
    exists(WebContextParameter parameter |
      // Find a web context parameter in the same file and ...
      parameter.getFile() = this and
      // ... with the right name.
      name = parameter.getParamName().getValue() and
      result = parameter.getParamValue().getValue()
    )
  }
}

/**
 * An XML element in a `WebXMLFile`.
 */
class WebXMLElement extends XMLElement {
  WebXMLElement() {
    this.getFile() instanceof WebXMLFile
  }

  /**
   * Gets the value for this element, with leading and trailing whitespace trimmed.
   */
  string getValue() {
    result = allCharactersString().trim()
  }
}

/**
 * A `<context-param>` element in a `web.xml` file.
 */
class WebContextParameter extends WebXMLElement {
  WebContextParameter() {
    this.getName() = "context-param"
  }

  /**
   * Gets the `<param-name>` element of this `<context-param>`.
   */
  WebContextParamName getParamName() {
    result = getAChild()
  }

  /**
   * Gets the `<param-value>` element of this `<context-param>`.
   */
  WebContextParamValue getParamValue() {
    result = getAChild()
  }
}

/**
 * A `<param-name>` element in a `web.xml` file.
 */
class WebContextParamName extends WebXMLElement {
  WebContextParamName() {
    getName() = "param-name"
  }
}

/**
 * A `<param-value>` element in a `web.xml` file.
 */
class WebContextParamValue extends WebXMLElement {
  WebContextParamValue() {
    getName() = "param-value"
  }
}

/**
 * A `<filter>` element in a `web.xml` file.
 */
class WebFilter extends WebXMLElement {
  WebFilter() {
    getName() = "filter"
  }
}

/**
 * A `<filter-class>` element in a `web.xml` file, nested under a `<filter>` element.
 */
class WebFilterClass extends WebXMLElement {
  WebFilterClass() {
    getName() = "filter-class" and
    getParent() instanceof WebFilter
  }

  Class getClass() {
    result.getQualifiedName() = getValue()
  }
}

/**
 * A `<servlet>` element in a `web.xml` file.
 */
class WebServlet extends WebXMLElement {
  WebServlet() {
    getName() = "servlet"
  }
}

/**
 * A `<servlet-class>` element in a `web.xml` file, nested under a `<servlet>` element.
 */
class WebServletClass extends WebXMLElement {
  WebServletClass() {
    getName() = "servlet-class" and
    getParent() instanceof WebServlet
  }

  Class getClass() {
    result.getQualifiedName() = getValue()
  }
}

/**
 * A `<listener>` element in a `web.xml` file.
 */
class WebListener extends WebXMLElement {
  WebListener() {
    getName() = "listener"
  }
}

/**
 * A `<listener-class>` element in a `web.xml` file, nested under a `<listener>` element.
 */
class WebListenerClass extends WebXMLElement {
  WebListenerClass() {
    getName() = "listener-class" and
    getParent() instanceof WebListener
  }

  /**
   * Gets the `Class` instance associated with this element.
   */
  Class getClass() {
    result.getQualifiedName() = getValue()
  }
}
