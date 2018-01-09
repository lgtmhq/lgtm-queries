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

import python


predicate monkey_patched_builtin(string name) {
    exists(AttrNode attr, SubscriptNode subscr, StrConst s | 
        subscr.isStore() and
        subscr.getIndex().getNode() = s and
        s.getText() = name and
        subscr.getValue() = attr and
        attr.getObject("__dict__").refersTo(theBuiltinModuleObject())
    )
    or
    exists(CallNode call, ControlFlowNode bltn, StrConst s | 
        call.getArg(0) = bltn and
        bltn.refersTo(theBuiltinModuleObject()) and
        call.getArg(1).getNode() = s and
        s.getText() = name and
        call.getFunction().refersTo(builtin_object("setattr"))
    )
    or
    exists(AttrNode attr | 
        attr.isStore() and
        attr.getObject(name).refersTo(theBuiltinModuleObject())
    )
}
