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
 * @name Unguarded next in generator
 * @description Calling next() in a generator may cause unintended early termination of an iteration.
 * @kind problem
 * @tags maintainability
 *       portability
 * @problem.severity warning
 * @sub-severity low
 * @precision very-high
 */

import python

FunctionObject iter() {
    result = builtin_object("iter")
}

FunctionObject next() {
    result = builtin_object("next")
}

predicate call_to_iter(CallNode call, Object sequence) {
    iter().getArgumentForCall(call, 0).refersTo(sequence)
}

predicate call_to_next(CallNode call, Object iterator) {
    next().getArgumentForCall(call, 0).refersTo(iterator)
}

predicate guarded_not_empty_sequence(Object sequence) {
    exists(IsTrue guard, ControlledVariable var, NameNode use |
        use = var.getAUse() |
        use.refersTo(sequence) and
        guard.controls(var, use.getBasicBlock(), true)
    )
}

/** The pattern `next(iter(x))` is often used where `x` is known not be empty. Check for that. */
predicate iter_not_exhausted(Object iterator) {
    exists(Object sequence |
        call_to_iter(iterator, sequence) and
        guarded_not_empty_sequence(sequence)
    )
}


from CallNode call, Object iterator
where call_to_next(call, iterator) and
call.getNode().getScope().(Function).isGenerator() and
not iter_not_exhausted(iterator)

select call, "Call to next() in a generator"

