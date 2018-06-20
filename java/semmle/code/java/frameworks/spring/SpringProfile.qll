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
import semmle.code.java.frameworks.spring.SpringComponentScan

/**
 * An expression used as a profile description somewhere in the program, i.e. in a Spring beans
 * XML configuration file, or as an argument to a `@Profile` annotation.
 *
 * There are two valid forms of profile expression `<profile>` and `!<profile>`, where `<profile>`
 * is a string defining a profile name. The former is active if the profile is active, and the
 * latter is active if the profile is not active.
 */
class SpringProfileExpr extends string {
  SpringProfileExpr() {
    exists(SpringBeanFile beanFile | this = beanFile.getAProfileExpr()) or
    exists(SpringComponent springComponent | this = springComponent.getAProfileExpr())
  }

  /**
   * The profile described in this profile expression.
   */
  string getProfile() {
    result = this
  }

  /**
   * This profile expression is active if it can ever be evaluated to true, according to our
   * knowledge of which profiles are sometimes/never/always enabled.
   */
  predicate isActive() {
    (
      getProfile() instanceof AlwaysEnabledSpringProfile or
      getProfile() instanceof SometimesEnabledSpringProfile
    ) and
    not getProfile() instanceof NeverEnabledSpringProfile
  }
}

/**
 * A Spring profile expression that begins with "!", indicating a negated expression.
 */
class NotSpringProfileExpr extends SpringProfileExpr {
  NotSpringProfileExpr() {
    this.prefix(1) = "!"
  }

  /**
   * The profile described in this profile expression.
   */
  override string getProfile() {
    result = this.substring(1, this.length())
  }

  /**
   * This profile expression is active if it can ever be evaluated to true, according to our
   * knowledge of which profiles are sometimes/never/always enabled.
   */
  override predicate isActive() {
    not getProfile() instanceof AlwaysEnabledSpringProfile
  }
}

/**
 * A Spring profile observed somewhere in the program.
 */
class SpringProfile extends string {
  SpringProfile() {
    exists(SpringProfileExpr springProfileExpr |
      this = springProfileExpr.getProfile()
    )
  }
}


/**
 * A Spring profile that is always enabled.
 */
abstract class AlwaysEnabledSpringProfile extends string {
  bindingset[this]
  AlwaysEnabledSpringProfile() {
    this.length() < 100
  }
}

/**
 * A Spring profile that is sometimes enabled.
 *
 * Includes all `SpringProfile`s that are not specified as always enabled or never enabled.
 */
class SometimesEnabledSpringProfile extends string {
  SometimesEnabledSpringProfile() {
    this instanceof SpringProfile and
    not (
      this instanceof AlwaysEnabledSpringProfile or
      this instanceof NeverEnabledSpringProfile
    )
  }
}


/**
 * A Spring profile that is never enabled.
 */
abstract class NeverEnabledSpringProfile extends string {
  bindingset[this]
  NeverEnabledSpringProfile() {
    this.length() < 100
  }
}
