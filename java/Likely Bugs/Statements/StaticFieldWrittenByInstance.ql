// Copyright 2016 Semmle Ltd.
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
 * @name Static field written by instance method
 * @description Writing to a static field from an instance method is prone to race conditions 
 *              unless you use synchronization. In addition, it makes it difficult to keep the 
 *              static state consistent and affects code readability.
 * @kind problem
 * @problem.severity warning
 */
import default

from FieldWrite fw, Field f, Callable c, string kind
where fw.getField() = f and
      f.isStatic() and
      c = fw.getSite() and
      not c.isStatic() and
      f.getDeclaringType() = c.getDeclaringType() and
      c.fromSource() and
      if c instanceof Constructor then kind = "constructor for" else kind = "instance method"
select fw, "Write to static field " + f.getName() + " in " + kind + " " + c.getName() + "."
