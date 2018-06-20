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

import default

/**
 * A Java Server Faces `ManagedBean` annotation on a class.
 */
class FacesManagedBeanAnnotation extends Annotation {
  FacesManagedBeanAnnotation() {
    getType().hasQualifiedName("javax.faces.bean", "ManagedBean")
  }

  /**
   * Get the `Class` of the managed bean.
   */
  Class getManagedBeanClass() {
    result = getAnnotatedElement()
  }
}

/**
 * A Java Server Faces `FacesComponent` annotation on a class.
 *
 * This registers the class as a new `UIComponent`, that can be used in views (JSP or facelets).
 */
class FacesComponentAnnotation extends Annotation {
  FacesComponentAnnotation() {
    getType().hasQualifiedName("javax.faces.component", "FacesComponent")
  }

  /**
   * Get the `Class` of the FacesComponent, if this annotation is valid.
   */
  Class getFacesComponentClass() {
    result = getAnnotatedElement()
  }
}