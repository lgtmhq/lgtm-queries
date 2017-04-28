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
 * Provides classes and predicates for identifying GWT UiBinder framework XML templates.
 */

import java

/** A GWT UiBinder XML template file with a `.ui.xml` suffix. */
class GwtUiTemplateXmlFile extends XMLFile {
  GwtUiTemplateXmlFile() {
    this.getName().matches("%.ui.xml")
  }

  /** The top-level UiBinder element. */
  GwtUiBinderTemplateElement getUiBinderElement() {
    result = this.getAChild()
  }
}

/** The top-level `<ui:UiBinder>` element of a GWT UiBinder template XML file. */
class GwtUiBinderTemplateElement extends XMLElement {
  GwtUiBinderTemplateElement() {
    this.getParent() instanceof GwtUiTemplateXmlFile and
    this.getName() = "UiBinder" and
    this.getNamespace().getURI() = "urn:ui:com.google.gwt.uibinder"
  }
}

/**
 * A component reference within a GWT UiBinder template.
 */
class GwtComponentTemplateElement extends XMLElement {
  GwtComponentTemplateElement() {
    exists(GwtUiBinderTemplateElement templateElement |
      this = templateElement.getAChild*() |
      this.getNamespace().getURI().substring(0, 10) = "urn:import"
    )
  }

  /**
   * The class represented by this element.
   */
  Class getClass() {
    exists(string namespace |
      namespace = getNamespace().getURI() and
      result.getQualifiedName() = namespace.substring(11, namespace.length()) + "." + getName()
    )
  }
}
