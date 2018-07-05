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
 * Provides classes and predicates for working with annotations from the `JUnit` framework.
 */

import java

/*
 * Annotations in the `org.junit` package.
 */

/**
 * An `@org.junit.After` annotation.
 */
class AfterAnnotation extends Annotation {
  AfterAnnotation() {
    this.getType().hasQualifiedName("org.junit", "After")
  }
}

/**
 * An `@org.junit.AfterClass` annotation.
 */
class AfterClassAnnotation extends Annotation {
  AfterClassAnnotation() {
    this.getType().hasQualifiedName("org.junit", "AfterClass")
  }
}

/**
 * An `@org.junit.Before` annotation.
 */
class BeforeAnnotation extends Annotation {
  BeforeAnnotation() {
    this.getType().hasQualifiedName("org.junit", "Before")
  }
}

/**
 * An `@org.junit.BeforeClass` annotation.
 */
class BeforeClassAnnotation extends Annotation {
  BeforeClassAnnotation() {
    this.getType().hasQualifiedName("org.junit", "BeforeClass")
  }
}

/**
 * An `@org.junit.Ignore` annotation.
 */
class IgnoreAnnotation extends Annotation {
  IgnoreAnnotation() {
    this.getType().hasQualifiedName("org.junit", "Ignore")
  }
}

/**
 * An `@org.junit.Test` annotation.
 */
class TestAnnotation extends Annotation {
  TestAnnotation() {
    this.getType().hasQualifiedName("org.junit", "Test")
  }
}

/*
 * Annotations in the `org.junit.runner` package.
 */

/**
 * An `@org.junit.runner.RunWith` annotation, which indicates that
 * tests within a class should be run with a special `Runner`.
 */
class RunWithAnnotation extends Annotation {
  RunWithAnnotation() {
    this.getType().hasQualifiedName("org.junit.runner", "RunWith")
  }

  /**
   * Gets the runner that will be used.
   */
  Type getRunner() {
    result = getValue("value").(TypeLiteral).getTypeName().getType()
  }
}
