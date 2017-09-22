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
 * @name Static array access may cause overflow
 * @description Exceeding the size of a static array during write or access operations
 *              may result in a buffer overflow.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @tags reliability
 *       security
 *       external/cwe/cwe-119
 *       external/cwe/cwe-131
 */
import default
import LoopBounds

predicate staticBuffer(Variable v, int size)
{
  exists(ArrayType t |
    v.getType() = t and
    t.getArraySize() = size and
    t.getBaseType() instanceof CharType)
}

class BufferAccess extends ArrayExpr
{
  BufferAccess() {
    exists(Variable v, int size |
      size != 0 and
      staticBuffer(v, size) and
      this.getArrayBase() = v.getAnAccess()
    ) and

    // exclude accesses in macro implementation of `strcmp`,
    // which are carefully controlled but can look dangerous.
    not exists(Macro m |
      m.getName() = "strcmp" and
      m.getAnInvocation().getAnExpandedElement() = this
    )
  }

  int bufferSize() {
    exists (Variable v |
      staticBuffer(v, result) and this.getArrayBase() = v.getAnAccess())
  }

  Variable buffer() {
    result.getAnAccess() = this.getArrayBase()
  }
}

predicate overflowOffsetInLoop(BufferAccess bufaccess, string msg)
{
  exists(ClassicForLoop loop |
    loop.getStmt().getAChild*() = bufaccess.getEnclosingStmt() and
    loop.limit() >= bufaccess.bufferSize() and
    loop.counter().getAnAccess() = bufaccess.getArrayOffset() and
    msg = "Potential buffer-overflow: counter '" + loop.counter().toString()
      + "' <= " + loop.limit().toString() + " but '" + bufaccess.buffer().getName()
      + "' has " + bufaccess.bufferSize().toString() + " elements.")
}

predicate bufferAndSizeFunction(Function f, int buf, int size)
{
  (f.hasQualifiedName("read") and buf = 1 and size = 2) or
  (f.hasQualifiedName("fgets") and buf = 0 and size = 1) or
  (f.hasQualifiedName("strncpy") and buf = 0 and size = 2) or
  (f.hasQualifiedName("strncat") and buf = 0 and size = 2) or
  (f.hasQualifiedName("memcpy") and buf = 0 and size = 2) or
  (f.hasQualifiedName("memmove") and buf = 0 and size = 2) or
  (f.hasQualifiedName("snprintf") and buf = 0 and size = 1) or
  (f.hasQualifiedName("vsnprintf") and buf = 0 and size = 1)
}

class CallWithBufferSize extends FunctionCall
{
  CallWithBufferSize() { bufferAndSizeFunction(this.getTarget(), _, _) }
  Expr buffer() {
    exists(int i |
      bufferAndSizeFunction(this.getTarget(), i, _) and
      result = this.getArgument(i))
  }
  Expr statedSize() {
    exists(int i |
      bufferAndSizeFunction(this.getTarget(), _, i) and
      result = this.getArgument(i))
  }
}

predicate wrongBufferSize(Expr error, string msg) {
  exists(CallWithBufferSize call, int bufsize, Variable buf |
    staticBuffer(buf, bufsize) and
    call.buffer() = buf.getAnAccess() and
    call.statedSize().getValue().toInt() > bufsize and
    error = call.statedSize() and
    msg = "Potential buffer-overflow: '" + buf.getName() +
    "' has size " + bufsize.toString() + " not " + call.statedSize().getValue() + ".")
}

predicate outOfBounds(BufferAccess bufaccess, string msg)
{
  exists(int size, int access, string buf |
    buf = bufaccess.buffer().getName() and
    bufaccess.bufferSize() = size and
    bufaccess.getArrayOffset().getValue().toInt() = access and
    ( access > size or
     (access = size and not exists(AddressOfExpr addof | bufaccess = addof.getOperand()))) and
    msg = "Potential buffer-overflow: '" + buf + "' has size " + size.toString() +
      " but '" + buf + "[" + access.toString() + "]' is accessed here.")
}

from Element error, string msg
where overflowOffsetInLoop(error, msg)
   or wrongBufferSize(error, msg)
   or outOfBounds(error, msg)
select error, msg
