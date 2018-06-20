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
 * Cucumber is an open-source project for writing executable acceptance tests in human-readable `.feature` files.
 */
import java

/**
 * An annotation defined in the Cucumber library.
 */
class CucumberAnnotation extends Annotation {
  CucumberAnnotation() {
    getType().getPackage().getName().matches("cucumber.api.java%")
  }
}

/**
 * A Cucumber interface for a specific language.
 */
class CucumberJava8Language extends Interface {
  CucumberJava8Language() {
    getASupertype().getAnAncestor().hasQualifiedName("cucumber.runtime.java8", "LambdaGlueBase")
  }
}

/**
 * A step definition for Cucumber.
 */
class CucumberStepDefinition extends Method {
  CucumberStepDefinition() {
    getAnAnnotation() instanceof CucumberAnnotation
  }
}

/**
 * A class containing Cucumber step definitions.
 */
class CucumberStepDefinitionClass extends Class {
  CucumberStepDefinitionClass() {
    getAMember() instanceof CucumberStepDefinition
  }
}
