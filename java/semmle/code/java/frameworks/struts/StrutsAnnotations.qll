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
 * An annotation in the struts 2 convention plugin.
 */
class StrutsAnnotation extends Annotation {
  StrutsAnnotation() {
    this.getType().getPackage().hasName("org.apache.struts2.convention.annotation")
  }
}

/**
 * A struts annotation that signifies the annotated method should be treated as an action.
 */
class StrutsActionAnnotation extends StrutsAnnotation {
  StrutsActionAnnotation() {
    this.getType().hasName("Action")
  }

  Callable getActionCallable() {
    result = getAnnotatedElement() or
    exists(StrutsActionsAnnotation actions |
      this = actions.getAnAction() |
      result = actions.getAnnotatedElement()
    )
  }
}

/**
 * A struts annotation that represents a group of actions for the annotated method.
 */
class StrutsActionsAnnotation extends StrutsAnnotation {
  StrutsActionsAnnotation() {
    this.getType().hasName("Actions")
  }

  /**
   * Gets an Action annotation contained in this Actions annotation.
   */
  StrutsActionAnnotation getAnAction() {
    result = this.getAValue("value")
  }
}