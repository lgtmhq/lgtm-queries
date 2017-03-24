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

import semmle.python.dependencies.Dependencies

/**
 * A library describing an abstract mechanism for representing dependency categories.
 */

/*
 * A DependencyCategory is a unique string key used by Architect to identify different categories
 * of dependencies that might be viewed independently.
 * <p>
 * The string key defining the category must adhere to the isValid(), otherwise it will not be
 * accepted by Architect.
 * </p>
 */
abstract class DependencyKind extends string {

    bindingset[this]
    DependencyKind() {
        this = this
    }

    /* Tech inventory interface */
    /**
   * Identify dependencies associated with this category.
   * <p>
   * The source element is the source of the dependency.
   * </p>
   */
    abstract predicate isADependency(AstNode source, Object target);

}