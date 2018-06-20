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

import semmle.code.java.frameworks.spring.SpringBean
import semmle.code.java.frameworks.spring.SpringBeanFile
import semmle.code.java.frameworks.spring.metrics.MetricSpringBean

class MetricSpringBeanFile extends SpringBeanFile {
  SpringBeanFile getASpringBeanFileDependency() {
    exists(SpringBean b1, SpringBean b2 |
      b1.getSpringBeanFile() = this and
      b2.getSpringBeanFile() = result and
      springDepends(b1, b2, _)
    )
  }

  int getAfferentCoupling() {
    result = count(MetricSpringBeanFile other | other.getASpringBeanFileDependency() = this)
  }

  int getEfferentCoupling() {
    result = count(this.getASpringBeanFileDependency())
  }
}
