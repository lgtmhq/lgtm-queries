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

import semmle.code.cpp.Element

/**
 * A delegate to compute metrics on an element.
 */
class MetricNamespace extends Namespace {

  /** the number of incoming dependencies */
  int getAfferentCoupling() {
    result = count(MetricNamespace that | that.getANamespaceDependency() = this)
  }

  /** the number of outgoing dependencies */
  int getEfferentCoupling() {
    result = count(MetricNamespace that | this.getANamespaceDependency() = that)
  }

  /** Instability
      Instability is a measure of how likely a package is to be influenced
      by changes to other packages. If this metric value is high, it is easily
      influenced, if it is low, the impact is likely to be minimal. Instability
      is estimated as the number of outgoing dependencies relative to the total
      number of depencies.
   */
  float getInstability() {
      exists(int ecoupling, int sumcoupling |
                 ecoupling = this.getEfferentCoupling() and
                 sumcoupling = ecoupling + this.getAfferentCoupling() and
                 sumcoupling > 0 and
                 result = ecoupling / ((float)sumcoupling))
  }

  /** Abstractness
      Abstractness measures the proportion of abstract types in
      a package relative to the total number of types in that package.
      A highly abstract package (where the metric value is close 1)
      that is furthermore instable is likely to be useless: the
      class hierarchy has been over-engineered, and all those
      abstract types are not heavily used.
   */
  float getAbstractness() {
      exists(int i, int j | i = count(Class c | c.getNamespace()=this) and
                            j = count(Class c | c.getNamespace()=this and
                                                c.isAbstract()) and
                            result = j / ((float)i) and i > 0)
  }

  /** Distance from Main Sequence
      This measure intends to capture the tradeoff between abstractness
      and instability: the ideal situation occurs when the sum of
      abstractness and instability is one. That is, a package is
      completely abstract and stable (abstractness=1 and instability=0)
      or it is concrete and instable (abstractness=0 and instability=1).
      We thus measure the distance from that ideal situation.
   */
  float getDistanceFromMain() {
      exists(float r |
        r = this.getAbstractness() + this.getInstability() - 1
        and
        ( (r >= 0 and result = r)
          or
          (r < 0 and result = -r) ) )
   }

     /** a namespace dependency of this element */
  MetricNamespace getANamespaceDependency() {
    exists(MetricClass c | c.getNamespace() = this
      and c.getAClassDependency().getNamespace() = result)
    or exists(FunctionCall c | c.getEnclosingFunction().getNamespace() = this
      and c.getTarget().getNamespace() = result)
    or exists(FunctionCall c | c.getEnclosingVariable().getNamespace() = this
      and c.getTarget().getNamespace() = result)
    or exists(Access a | a.getEnclosingFunction().getNamespace() = this
      and a.getTarget().getNamespace() = result)
    or exists(Access a | a.getEnclosingVariable().getNamespace() = this
      and a.getTarget().getNamespace() = result)
    or exists(Variable v, UserType t | v.getNamespace() = this
      and v.getType().refersTo(t) and t.getNamespace() = result)
    or exists(Function f, UserType t | f.getNamespace() = this
      and f.getType().refersTo(t) and t.getNamespace() = result)
  }
}


