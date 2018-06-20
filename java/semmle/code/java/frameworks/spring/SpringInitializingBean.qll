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
 * A class which implements the `InitializingBean` interface, directly or indirectly.
 *
 * If this class is used as a Spring bean, the `afterPropertiesSet()` method will be called after
 * bean initialization.
 */
class InitializingBeanClass extends Class {
  InitializingBeanClass() {
    getAnAncestor().hasQualifiedName("org.springframework.beans.factory", "InitializingBean")
  }

  /**
   * Get the `afterPropertiesSet()` method, which is called after the bean has been initialized.
   */
  Method getAfterPropertiesSet() {
    inherits(result) and
    result.hasName("afterPropertiesSet")
  }
}
