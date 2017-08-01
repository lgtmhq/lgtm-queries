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
 * Provides classes and predicates for working with the SnakeYaml serialization framework.
 */

import java
import semmle.code.java.security.DataFlow

/**
 * The class `org.yaml.snakeyaml.constructor.Constructor`.
 */
class SnakeYamlConstructor extends RefType {
  SnakeYamlConstructor() {
    this.hasQualifiedName("org.yaml.snakeyaml.constructor", "Constructor")
  }
}

/**
 * The class `org.yaml.snakeyaml.constructor.SafeConstructor`.
 */
class SnakeYamlSafeConstructor extends RefType {
  SnakeYamlSafeConstructor() {
    this.hasQualifiedName("org.yaml.snakeyaml.constructor", "SafeConstructor")
  }
}

/**
 * An instance of `SafeConstructor` or a `Constructor` that only allows the type that is passed into its argument.
 */
class SafeSnakeYamlConstruction extends FlowSource, ClassInstanceExpr {
  SafeSnakeYamlConstruction() {
    this.getConstructedType() instanceof SnakeYamlSafeConstructor or
    (
      this.getConstructedType() instanceof SnakeYamlConstructor and
      this.getNumArgument() > 0
    )
  }
}

/**
 * The class `org.yaml.snakeyaml.Yaml`.
 */
class Yaml extends RefType {
  Yaml() {
    this.hasQualifiedName("org.yaml.snakeyaml", "Yaml")
  }
}

/**
 * An instance of `Yaml` that does not allow arbitrary constructor to be called.
 */
class SafeYaml extends FlowSource, ClassInstanceExpr {
  SafeYaml() {
    this.getConstructedType() instanceof Yaml and
    exists(SafeSnakeYamlConstruction ssyc | ssyc.flowsTo(this.getArgument(0)))
  }
}

/**
 * A call to a parse method of `Yaml` that allows arbitrary constructor to be called.
 */
class UnsafeSnakeYamlParse extends MethodAccess {
  UnsafeSnakeYamlParse() {
    exists(Method m | m.getDeclaringType() instanceof Yaml and
      (m.hasName("load") or m.hasName("loadAll") or m.hasName("parse")) and
      m = this.getMethod()
    ) and
    not exists(SafeYaml sy | sy.flowsTo(this.getQualifier()))
  }
}