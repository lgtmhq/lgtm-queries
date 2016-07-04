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
 * @name Useless assignment to global variable
 * @description An assignment to a global variable that is never used has no effect.
 * @kind problem
 * @problem.severity warning
 */

import default

from Variable v, GlobalVarAccess gva
where v = gva.getVariable() and
      // every access to 'v' is a write
      forall (VarAccess va | va = v.getAnAccess() |
        exists (Assignment assgn | assgn.getTarget() = va)
      ) and
      // 'v' is not externally declared...
      not exists (ExternalVarDecl d | d.getName() = v.getName() |
        // ...as a member of {Window,Worker,WebWorker}.prototype
        d.(ExternalInstanceMemberDecl).getBaseName().regexpMatch("Window|Worker|WebWorker") or
        // ...or as a member of window
        d.(ExternalStaticMemberDecl).getBaseName() = "window" or
        // ...or as a global
        d instanceof ExternalGlobalDecl
      ) and
      // it isn't declared using a JSLint-style 'global' declaration
      not exists (JSLintGlobal decl | decl.appliesTo(gva) | decl.declaresGlobal(v.getName(), _)) and
      // ignore accesses under 'with', since they may well refer to properties of the with'ed object
      not exists (WithStmt with | gva.getEnclosingStmt().nestedIn(with))
select gva, "This statement assigns a value to " + v.getName() + " that is never read."
