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
 * @name Wrong number of arguments for format
 * @description A string formatting operation, such as '"%s: %s, %s" % (a,b)', where the number of conversion specifiers in the
 *              format string differs from the number of values to be formatted will raise a TypeError.
 * @kind problem
 * @tags reliability
 *       correctness
 * @problem.severity error
 * @sub-severity low
 * @precision very-high
 * @id py/percent-format/wrong-arguments
 */

import python
import semmle.python.strings

predicate string_format(BinaryExpr operation, StrConst str, Object args, AstNode origin) {
    exists(Object fmt | operation.getOp() instanceof Mod |
           operation.getLeft().refersTo(fmt, str) and
           operation.getRight().refersTo(args, origin)
    )
}

int sequence_length(Object args) {
    /* Guess length of sequence */
    exists(Tuple seq | 
        seq = args.getOrigin() | 
        result = strictcount(seq.getAnElt())
    )
    or
    exists(ImmutableLiteral i | 
        i.getLiteralObject() = args |
        result = 1
    )
}


from BinaryExpr operation, StrConst fmt, Object args, int slen, int alen, AstNode origin, string provided
where string_format(operation, fmt, args, origin) and slen = sequence_length(args) and alen = format_items(fmt) and slen != alen and
(if slen = 1 then provided = " is provided." else provided = " are provided.")
select operation, "Wrong number of $@ for string format. Format $@ takes " + alen.toString() + ", but " + slen.toString() + provided,
  origin, "arguments",
  fmt, fmt.getText()
