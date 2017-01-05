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
 * @name Missing super clone
 * @description A 'clone' method that is overridden in a subclass, and that does not itself call
 *              'super.clone', causes calls to the subclass's 'clone' method to return an object of
 *              the wrong type.
 * @kind problem
 * @problem.severity error
 * @tags reliability
 *       maintainability
 *       external/cwe/cwe-580
 */
import java

from CloneMethod c, CloneMethod sc
where c.callsSuper(sc) and 
      c.fromSource() and 
      exists(sc.getBody()) and
      not exists(CloneMethod ssc | sc.callsSuper(ssc))
select sc, "This clone method does not call super.clone(), but is "
          + "overridden and called $@.", c, "in a subclass"
