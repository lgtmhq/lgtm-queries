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
 * Provides classes and predicates for identifying uses of the GWT UiBinder framework.
 *
 * The UiBinder framework allows the specification of user interfaces in XML template files. These
 * can then be interacted with programmatically by writing an associated owner class.
 */

import java
import GwtUiBinderXml

class GwtUiBinderClientAnnotation extends Annotation {
  GwtUiBinderClientAnnotation() {
    getType().getPackage().hasName("com.google.gwt.uibinder.client")
  }
}

class GwtUiHandlerAnnotation extends GwtUiBinderClientAnnotation {
  GwtUiHandlerAnnotation() {
    getType().hasName("UiHandler")
  }
}

class GwtUiFieldAnnotation extends GwtUiBinderClientAnnotation {
  GwtUiFieldAnnotation() {
    getType().hasName("UiField")
  }
}

class GwtUiTemplateAnnotation extends GwtUiBinderClientAnnotation {
  GwtUiTemplateAnnotation() {
    getType().hasName("UiTemplate")
  }
}

class GwtUiFactoryAnnotation extends GwtUiBinderClientAnnotation {
  GwtUiFactoryAnnotation() {
    getType().hasName("UiFactory")
  }
}

class GwtUiConstructorAnnotation extends GwtUiBinderClientAnnotation {
  GwtUiConstructorAnnotation() {
    getType().hasName("UiConstructor")
  }
}

/**
 * A field that is reflectively written to, and read from, by the GWT UiBinder framework.
 */
class GwtUiField extends Field {
  GwtUiField() {
    getAnAnnotation() instanceof GwtUiFieldAnnotation
  }

  /**
   * If true, the field must be filled before `UiBinder.createAndBindUi` is called.
   * If false, `UiBinder.createAndBindUi` will fill the field.
   */
  predicate isProvided() {
    getAnAnnotation().(GwtUiFieldAnnotation).getValue("provided").(BooleanLiteral).getBooleanValue() = true
  }
}

/**
 * A method called as a handler for events thrown by GWT widgets.
 */
class GwtUiHandler extends Method {
  GwtUiHandler() {
    getAnAnnotation() instanceof GwtUiHandlerAnnotation
  }

  /**
   * Gets the name of the field for which this handler is registered.
   */
  string getFieldName() {
    result = getAnAnnotation().(GwtUiHandlerAnnotation).getValue("value").(CompileTimeConstantExpr).getStringValue()
  }

  /**
   * Gets the field for which this handler is registered, if the UiField is represented in this class.
   */
  GwtUiField getField() {
    result = this.getDeclaringType().getAField() and
    result.getName() = getFieldName()
  }
}

/**
 * A method that may be called by the UiBinder framework as a result of a `GWT.create()` call, to
 * construct an instance of a class specified in a UiBinder XML file.
 */
class GwtUiFactory extends Method {
  GwtUiFactory() {
    getAnAnnotation() instanceof GwtUiFactoryAnnotation
  }
}

/**
 * A constructor that may be called by the UiBinder framework as a result of a `GWT.create()` call.
 */
class GwtUiConstructor extends Constructor {
  GwtUiConstructor() {
    getAnAnnotation() instanceof GwtUiConstructorAnnotation
  }
}
