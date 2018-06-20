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
 * Provides classes and predicates for identifying classes reflectively constructed by Selenium using the
 * `PageFactory.initElements(...)` method.
 */

import default
import semmle.code.java.Reflection

/**
 * The Selenium `PageFactory` class used to create page objects
 */
class SeleniumPageFactory extends Class {
  SeleniumPageFactory() {
    hasQualifiedName("org.openqa.selenium.support", "PageFactory")
  }
}

/**
 * A call to the Selenium `PageFactory.initElements` method, to construct a page object.
 */
class SeleniumInitElementsAccess extends MethodAccess {
  SeleniumInitElementsAccess() {
    getMethod().getDeclaringType() instanceof SeleniumPageFactory and
    getMethod().hasName("initElements")
  }

  /**
   * Get the class that is initialized by this call..
   */
  Class getInitClass() {
    result = inferClassParameterType(getArgument(1))
  }
}

/**
 * A class which is constructed by Selenium as a page object using `PageFactory.initElements(...)`.
 */
class SeleniumPageObject extends Class {
  SeleniumPageObject() {
    exists(SeleniumInitElementsAccess init |
      this = init.getInitClass()
    )
  }
}