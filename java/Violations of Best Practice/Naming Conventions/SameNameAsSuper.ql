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
 * @name Class has same name as super class
 * @description A class that has the same name as its superclass may be confusing.
 * @kind problem
 * @problem.severity recommendation
 * @tags maintainability
 *       readability
 *       naming
 */
import java

from RefType sub, RefType sup
where sub.fromSource() and
      sup = sub.getASupertype() and
      sub.getName() = sup.getName()
select sub, sub.getName() + " has the same name as its supertype $@.",
       sup, sup.getQualifiedName()
