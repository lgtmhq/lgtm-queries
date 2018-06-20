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
 * Provides classes and predicates for the Apache Camel Java annotations.
 *
 * Apache Camel allows "routes" to be defined in Java, using annotations. For example:
 *
 * ```
 * public class ConsumeMdb {
 *   @Consume(uri = "activemq:queue:sayhello")
 *   public String onMyMessage(String message) {
 *       return "Hello " + message;
 *   }
 * }
 * ```
 *
 * This creates a route to the `ConsumeMdb` class for messages sent to "activemq:queue:sayhello".
 */
import java
import semmle.code.java.Reflection
import semmle.code.java.frameworks.spring.Spring


library class CamelAnnotation extends Annotation {
  CamelAnnotation() {
    getType().getPackage().hasName("org.apache.camel")
  }
}

/**
 * An annotation indicating that the annotated method is called by Apache Camel.
 */
class CamelConsumeAnnotation extends CamelAnnotation {
  CamelConsumeAnnotation() {
    getType().hasName("Consume")
  }
}

/**
 * A method that may be called by Apache Camel in response to a message.
 */
class CamelConsumeMethod extends Method {
  CamelConsumeMethod() {
    getAnAnnotation() instanceof CamelConsumeAnnotation
  }
}
