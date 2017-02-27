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
 * A library for working with Java packages.
 */

import AST
import Element
import Type
import metrics.MetricPackage

/**
 * Whether element `e` is a descendant
 * of package `p` in the syntax tree.
 *
 * DEPRECATED: use `Element.contains` instead.
 */
deprecated
predicate isInPackage(Element e, Package p) {
  hasChild+(p,e)
}

/**
 * A package may be used to abstract over all of its members,
 * regardless of which compilation unit they are defined in.
 */
class Package extends Element, Annotatable, @package {
  /** A top level type in this package. */
  TopLevelType getATopLevelType() { result.getPackage() = this }

  /** Whether at least one reference type in this package originates from source code. */
  predicate fromSource() { 
    exists(RefType t | t.fromSource() and t.getPackage() = this) 
  }

  /** Cast this package to a class that provides access to metrics information. */
  MetricPackage getMetrics() { result = this }
  
  /**
   * A dummy URL for packages.
   *
   * This declaration is required to allow selection of packages in QL queries.
   * Without it, an implicit call to `Package.getLocation()` would be generated
   * when selecting a package, which would result in a compile-time error
   * since packages do not have locations.
   */
  string getURL() { result = "file://:0:0:0:0" }
}
