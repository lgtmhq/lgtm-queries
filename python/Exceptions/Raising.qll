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

import python

/** Whether the raise statement 'r' raises 'type' from origin 'orig' */ 
predicate type_or_typeof(Raise r, ClassObject type, ControlFlowNode orig) {
     exists(RaisingNode raise, ControlFlowNode exception |
        raise.getNode() = r and
        exception = raise.getExceptionNode() |
        exception.refersTo(type, _, orig)
        or
        not exists(ClassObject exc_type | exception.refersTo(exc_type)) and
        not type = theTypeType() and // First value is an unknown exception type
        exception.refersTo(_, type, orig)
    )
  
}