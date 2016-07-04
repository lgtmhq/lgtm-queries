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
 * @name AnnotationPresent check
 * @description If an annotation has not been annotated with a 'RUNTIME' retention policy, checking 
 *              for its presence at runtime is not possible.
 * @kind problem
 * @problem.severity error
 */
import default

from MethodAccess c, Method m, ParameterizedClass p, AnnotationType t
where c.getMethod() = m and
  m.hasName("isAnnotationPresent") and
  m.getNumberOfParameters() = 1 and
  c.getArgument(0).getType() = p and
  p.getATypeArgument() = t and
  not exists(Annotation a | 
    t.getAnAnnotation() = a and 
    a.getType().hasQualifiedName("java.lang.annotation", "Retention") and
    a.getAValue().(VarAccess).getVariable().hasName("RUNTIME")
  )
select c, "Call to isAnnotationPresent where no annotation has the RUNTIME retention policy."
