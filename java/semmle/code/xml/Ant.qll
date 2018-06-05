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
 * Provides classes and predicates for working with targets in Apache Ant build files.
 */

import XML

/** An XML element that represents an Ant target. */
class AntTarget extends XMLElement {
  AntTarget() { super.getName() = "target" }

  /** The name of this Ant target. */
  override string getName() { result = this.getAttributeValue("name") }

  /**
   * A string containing the dependencies of this Ant target,
   * without whitespace and with a leading and trailing comma.
   *
   * This is a utility method used for extracting individual dependencies.
   */
  string getDependsString() {
    result = "," +
      this.getAttributeValue("depends").replaceAll(" ", "")
          .replaceAll("\r","").replaceAll("\n","").replaceAll("\t","") + ","
  }

  /** Holds if this Ant target depends on the specified target. */
  predicate dependsOn(AntTarget that) {
    this.getFile() = that.getFile() and
    this.getDependsString().matches("%,"+that.getName()+",%")
  }

  /** An Ant target on which this Ant target depends. */
  AntTarget getADependency() {
    this.dependsOn(result)
  }
}

/** An Ant target that occurs in an Ant build file with the default name `build.xml`. */
class MainAntTarget extends AntTarget {
  MainAntTarget() { this.getFile().getBaseName() = "build.xml" }
}
