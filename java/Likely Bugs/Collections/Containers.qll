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

import semmle.code.java.Collections
import semmle.code.java.Maps

/**
 * Containers are an abstraction of collections and maps.
 */
class ContainerType extends RefType {
  ContainerType() {
    this instanceof CollectionType or
    this instanceof MapType
  }
}

class ContainerMutator extends Method {
  ContainerMutator() {
    this instanceof CollectionMutator or
    this instanceof MapMutator
  }
}

class ContainerMutation extends MethodAccess {
  ContainerMutation() {
    this instanceof CollectionMutation or
    this instanceof MapMutation
  }
  
  predicate resultIsChecked() {
    this.(CollectionMutation).resultIsChecked() or
    this.(MapMutation).resultIsChecked()
  }  
}

class ContainerQueryMethod extends Method {
  ContainerQueryMethod() {
    this instanceof CollectionQueryMethod or
    this instanceof MapQueryMethod
  }
}

class FreshContainer extends ClassInstanceExpr {
  FreshContainer() {
    this instanceof FreshCollection or
    this instanceof FreshMap
  }
}
