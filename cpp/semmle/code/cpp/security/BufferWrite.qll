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

/**
 * @name CWE-120
 * @description Buffer Copy without Checking Size of Input ('Classic Buffer Overflow').
 * @kind problem
 * @problem.severity recommendation
 */
import cpp
import semmle.code.cpp.commons.Alloc
import semmle.code.cpp.commons.Buffer
import semmle.code.cpp.commons.Scanf
import semmle.code.cpp.commons.Strcat

// --- BufferWrite framework ---

/**
 * An operation that writes a variable amount of data to a buffer
 * (strcpy, strncat, sprintf etc).
 * 
 * Note that there are two related class frameworks:
 *  - BufferWrite provides detailed coverage of null-terminated
 *    buffer write operations.
 *  - BufferAccess provides general coverage of buffer read and write
 *    operations whose size is either not data-dependent, or has an upper
 *    bound which is not data-dependent.
 * This design has some overlaps between the two classes, for example
 * the write of a 'strncpy'.
 */
abstract class BufferWrite extends Expr
{
  // --- derived classes override these ---

  /** a data source (e.g. the source string, format string; not necessarily copied as-is) */
  Expr getASource() { none() }

  /** the destination buffer */
  abstract Expr getDest();

  /** does the operation have an explicit parameter that limits the amount of data written
      (e.g. strncpy does, whereas strcpy doesn't); this is not the same as exists(getExplicitLimit())
      because the limit may exist but be unknown at compile time. */
  predicate hasExplicitLimit() { none() }
  
  /** returns the explicit limit (in bytes, if it exists and is known) */
  int getExplicitLimit() { none() }
  
  /** returns an upper bound to the amount of data that's being written (if it can be found) */
  int getMaxData() { none() }

  /** as getMaxData() except that float to string conversions are assumed to be much smaller (8 bytes) than their true
      maximum length.  This can be helpful in determining the cause of a buffer overflow issue. */
  int getMaxDataLimited() { result = getMaxData() }

  /** describes the buffer write */
  string getBWDesc()
  {
    result = toString()
  }
}

/**
 * A `BufferWrite` that is also a `FunctionCall` (most cases).
 */
abstract class BufferWriteCall extends BufferWrite, FunctionCall
{
  Location getLocation() { result = FunctionCall.super.getLocation() }
  Type getType() { result = FunctionCall.super.getType() }
  string toString() { result = FunctionCall.super.toString() }
  predicate mayBeImpure() { FunctionCall.super.mayBeImpure() }
  predicate mayBeGloballyImpure() { FunctionCall.super.mayBeGloballyImpure() }
  int getPrecedence() { result = FunctionCall.super.getPrecedence() }
}

// --- BufferWrite classes ---

/**
 * A call to a variant of `strcpy`. 
 */
class StrCopyBW extends BufferWriteCall
{
  StrCopyBW()
  {
    exists(TopLevelFunction fn, string name | (fn = getTarget()) and (name = fn.getName()) and (
      (name = "strcpy")                       // strcpy(dst, src)
      or (name = "wcscpy")                    // wcscpy(dst, src)
      or (name = "_mbscpy")                   // _mbscpy(dst, src)
      or (
        (
          name = "strcpy_s" or                // strcpy_s(dst, max_amount, src)
          name = "wcscpy_s" or                // wcscpy_s(dst, max_amount, src)
          name = "_mbscpy_s"                  // _mbscpy_s(dst, max_amount, src)
        ) and
        fn.getNumberOfParameters() = 3        // exclude the 2-parameter template versions
                                              // that find the size of a fixed size destination buffer.
      )
      or (name = "strncpy")                   // strncpy(dst, src, max_amount)
      or (name = "strncpy_l")                 // strncpy_l(dst, src, max_amount, locale)
      or (name = "wcsncpy")                   // wcsncpy(dst, src, max_amount)
      or (name = "_wcsncpy_l")                // _wcsncpy_l(dst, src, max_amount, locale)
      or (name = "_mbsncpy")                  // _mbsncpy(dst, src, max_amount)
      or (name = "_mbsncpy_l")                // _mbsncpy_l(dst, src, max_amount, locale)
    ))
  }

  int getParamSize()
  {
    exists(TopLevelFunction fn, string name | (fn = getTarget()) and (name = fn.getName()) and (
      if (name.suffix(name.length() - 2) = "_s") then (
        result = 1
      ) else if exists(name.indexOf("ncpy")) then (
        result = 2
      ) else (
        none()
      )
    ))
  }
  
  int getParamSrc()
  {
    exists(TopLevelFunction fn, string name | (fn = getTarget()) and (name = fn.getName()) and (
      if (name.suffix(name.length() - 2) = "_s") then (
        result = 2
      ) else (
        result = 1
      )
    ))
  }

  int getCharSize()
  {
    exists(TopLevelFunction fn, string name | (fn = getTarget()) and (name = fn.getName()) and (
      if exists(name.indexOf("wcs")) then (
        exists(Type t | (t instanceof Wchar_t) and (result = t.getSize()))
      ) else (
        exists(Type t | (t instanceof PlainCharType) and (result = t.getSize()))
      )
    ))
  }

  Expr getASource()
  {
    result = getArgument(getParamSrc())
  }

  Expr getDest()
  {
    result = getArgument(0)
  }

  predicate hasExplicitLimit()
  {
    exists(getParamSize())
  }

  int getExplicitLimit()
  {
    result = getArgument(getParamSize()).getValue().toInt() * getCharSize()
  }

  int getMaxData()
  {
    result = getArgument(getParamSrc()).(AnalysedString).getMaxLength() * getCharSize()
  }
}

/**
 * A call to a variant of `strcat`. 
 */
class StrCatBW extends BufferWriteCall
{
  StrCatBW()
  {
    exists(TopLevelFunction fn | fn = getTarget() and fn instanceof StrcatFunction)
  }
  
  int getParamSize()
  {
    if exists(getArgument(2)) then (
      result = 2
    ) else (
      none()
    )
  }
  
  int getParamSrc()
  {
    result = 1
  }

  int getCharSize()
  {
    exists(TopLevelFunction fn, string name | (fn = getTarget()) and (name = fn.getName()) and (
      if exists(name.indexOf("wcs")) then (
        exists(Type t | (t instanceof Wchar_t) and (result = t.getSize()))
      ) else (
        exists(Type t | (t instanceof PlainCharType) and (result = t.getSize()))
      )
    ))
  }

  Expr getASource()
  {
    result = getArgument(getParamSrc())
  }

  Expr getDest()
  {
    result = getArgument(0)
  }

  predicate hasExplicitLimit()
  {
    exists(getParamSize())
  }

  int getExplicitLimit()
  {
    result = getArgument(getParamSize()).getValue().toInt() * getCharSize()
  }

  int getMaxData()
  {
    result = getArgument(getParamSrc()).(AnalysedString).getMaxLength() * getCharSize()
  }
}

/**
 * A call to a variant of `sprintf`. 
 */
class SprintfBW extends BufferWriteCall
{
  SprintfBW()
  {
    exists(TopLevelFunction fn, string name | (fn = getTarget()) and (name = fn.getName()) and (
      // C sprintf variants
      (name = "sprintf")                      // sprintf(dst, format, args...)
      or (name = "vsprintf")                  // vsprintf(dst, format, va_list)
      or (name = "wsprintf")                  // wsprintf(dst, format, args...)
      or (name = "vwsprintf")                 // vwsprintf(dst, format, va_list)
  
      // Microsoft sprintf variants
      or (name.regexpMatch("_sprintf_l"))     //  _sprintf_l(dst, format, locale, args...)
      or (name.regexpMatch("_vsprintf_l"))    //  _vsprintf_l(dst, format, locale, va_list))
      or (name.regexpMatch("__swprintf_l"))   // __swprintf_l(dst, format, locale, args...)
      or (name.regexpMatch("__vswprintf_l"))  // __vswprintf_l(dst, format, locale, va_list)
    ))
  }

  int getCharSize()
  {
    exists(TopLevelFunction fn, string name | (fn = getTarget()) and (name = fn.getName()) and (
      if (exists(name.indexOf("wprintf"))
          or exists(name.indexOf("wsprintf"))) then (
        exists(Type t | (t instanceof Wchar_t) and (result = t.getSize()))
      ) else (
        exists(Type t | (t instanceof PlainCharType) and (result = t.getSize()))
      )
    ))
  }

  Expr getASource()
  {
    (result = this.(FormattingFunctionCall).getFormat())
    or
    (result = this.(FormattingFunctionCall).getFormatArgument(_))
  }

  Expr getDest()
  {
    result = getArgument(0)
  }

  int getMaxData()
  {
    exists(FormatLiteral fl |
      (fl = this.(FormattingFunctionCall).getFormat())
      and (result = fl.getMaxConvertedLength() * getCharSize())
    ) 
  }

  int getMaxDataLimited()
  {
    exists(FormatLiteral fl |
      (fl = this.(FormattingFunctionCall).getFormat())
      and (result = fl.getMaxConvertedLengthLimited() * getCharSize())
    )
  }
}

/**
 * A call to a variant of `snprintf`. 
 */
class SnprintfBW extends BufferWriteCall
{
  SnprintfBW()
  {
    exists(TopLevelFunction fn, string name | (fn = getTarget()) and (name = fn.getName()) and (
      // C snprintf variants
      (name = "snprintf")                     // snprintf(dst, max_amount, format, args...)
      or (name = "vsnprintf")                 // vsnprintf(dst, max_amount, format, va_list)
      or (name = "swprintf")                  // swprintf(dst, max_amount, format, args...)
      or (name = "vswprintf")                 // vswprintf(dst, max_amount, format, va_list)
    
      // Microsoft snprintf variants
      or (name = "sprintf_s")                 // sprintf_s(dst, max_amount, format, locale, args...)
      or (name = "vsprintf_s")                // vsprintf_s(dst, max_amount, format, va_list)
      or (name = "swprintf_s")                // swprintf_s(dst, max_amount, format, args...)
      or (name = "vswprintf_s")               // vswprintf_s(dst, max_amount, format, va_list)
  
      // Microsoft snprintf variants with '_'
      or (
        (name.regexpMatch("_v?sn?w?printf(_s)?(_p)?(_l)?"))
        and (not this instanceof SprintfBW)
      )
      // _sprintf_s_l(dst, max_amount, format, locale, args...)
      // _swprintf_l(dst, max_amount, format, locale, args...)
      // _swprintf_s_l(dst, max_amount, format, locale, args...)
      // _snprintf(dst, max_amount, format, args...)
      // _snprintf_l(dst, max_amount, format, locale, args...)
      // _snwprintf(dst, max_amount, format, args...)
      // _snwprintf_l(buffer, max_amount, format, locale, args...)
      // _vsprintf_s_l(dst, max_amount, format, locale, va_list)
      // _vsprintf_p(dst, max_amount, format, va_list)
      // _vsprintf_p_l(dst, max_amount, format, locale, va_list)
      // _vswprintf_l(dst, max_amount, format, locale, va_list)
      // _vswprintf_s_l(buffer, max_amount, format, locale, va_list)
      // _vswprintf_p(dst, max_amount, format, va_list)
      // _vswprintf_p_l(dst, max_amount, format, locale, va_list)
      // _vsnprintf(dst, max_amount, format, va_list)
      // _vsnprintf_l(dst, max_amount, format, locale, va_list)
      // _vsnwprintf(dst, max_amount, format, va_list)
      // _vsnwprintf_l(dst, max_amount, format, locale, va_list)
    ))
  }
  
  int getParamSize()
  {
    result = 1
  }

  int getCharSize()
  {
    exists(TopLevelFunction fn, string name | (fn = getTarget()) and (name = fn.getName()) and (
      if (exists(name.indexOf("wprintf"))
          or exists(name.indexOf("wsprintf"))) then (
        exists(Type t | (t instanceof Wchar_t) and (result = t.getSize()))
      ) else (
        exists(Type t | (t instanceof PlainCharType) and (result = t.getSize()))
      )
    ))
  }

  Expr getASource()
  {
    (result = this.(FormattingFunctionCall).getFormat())
    or
    (result = this.(FormattingFunctionCall).getFormatArgument(_))
  }

  Expr getDest()
  {
    result = getArgument(0)
  }

  predicate hasExplicitLimit()
  {
    exists(getParamSize())
  }

  int getExplicitLimit()
  {
    result = getArgument(getParamSize()).getValue().toInt() * getCharSize()
  }

  int getMaxData()
  {
    exists(FormatLiteral fl |
      (fl = this.(FormattingFunctionCall).getFormat())
      and (result = fl.getMaxConvertedLength() * getCharSize())
    )
  }

  int getMaxDataLimited()
  {
    exists(FormatLiteral fl |
      (fl = this.(FormattingFunctionCall).getFormat())
      and (result = fl.getMaxConvertedLengthLimited() * getCharSize())
    )
  }
}

/**
 * A call to a variant of `gets`. 
 */
class GetsBW extends BufferWriteCall
{
  GetsBW()
  {
    exists(TopLevelFunction fn, string name | (fn = getTarget()) and (name = fn.getName()) and (
      (name = "gets")                         // gets(dst)
      or (name = "fgets")                     // fgets(dst, max_amount, src_stream)
      or (name = "fgetws")                    // fgetws(dst, max_amount, src_stream)
    ))
  }

  int getParamSize()
  {
    if exists(getArgument(1)) then (
      result = 1
    ) else (
      none()
    )
  }

  int getCharSize()
  {
    exists(TopLevelFunction fn, string name | (fn = getTarget()) and (name = fn.getName()) and (
      if (name = "fgetws") then (
        exists(Type t | (t instanceof Wchar_t) and (result = t.getSize()))
      ) else (
        exists(Type t | (t instanceof PlainCharType) and (result = t.getSize()))
      )
    ))  
  }

  Expr getASource()
  {
    if exists(getArgument(2)) then (
      result = getArgument(2)
    ) else (
      result = this // the source is input inside the 'gets' call itself
    )
  }

  Expr getDest()
  {
    result = getArgument(0)
  }

  predicate hasExplicitLimit()
  {
    exists(getParamSize())
  }

  int getExplicitLimit()
  {
    result = getArgument(getParamSize()).getValue().toInt() * getCharSize()
  }
}

/**
 * A string that is written by a `scanf`-like function.
 */
class ScanfBW extends BufferWrite
{
  ScanfBW()
  {
    exists(ScanfFunctionCall fc, ScanfFormatLiteral fl, int arg, int args_pos |
      (this = fc.getArgument(arg))
      and (args_pos = fc.getTarget().getNumberOfParameters())
      and (arg >= args_pos)
      and (fl = fc.getFormat())
      and (fl.getConversionChar(arg - args_pos) = "s")
    )
  }

  int getParamArgs()
  {
    exists(FunctionCall fc | this = fc.getArgument(_)
      and (result = fc.getTarget().getNumberOfParameters())
    )
  }

  int getCharSize()
  {
    exists(ScanfFunctionCall fc | (this = fc.getArgument(_)) and
      if (fc.isWideCharDefault()) then (
        exists(Type t | (t instanceof Wchar_t) and (result = t.getSize()))
      ) else (
        exists(Type t | (t instanceof PlainCharType) and (result = t.getSize()))
      )
    )
  }

  Expr getASource()
  {
    exists(ScanfFunctionCall fc |
      (this = fc.getArgument(_)) and (
        // inputs are: the format string, input or the argument itself (if there's no explicit input) 
        (result = fc.getFormat()) or
        (result = fc.getArgument(fc.getInputParameterIndex())) or
        (not exists(fc.getInputParameterIndex()) and (result = this))
      )
    )
  }

  Expr getDest()
  {
    result = this
  }

  int getMaxData()
  {
    exists(ScanfFunctionCall fc, ScanfFormatLiteral fl, int arg |
      (this = fc.getArgument(arg))
      and (fl = fc.getFormat())
      and (result = (fl.getMaxConvertedLength(arg - getParamArgs()) + 1) * getCharSize()) // +1 is for the terminating null
    )
  }

  string getBWDesc()
  {
    exists(FunctionCall fc | (this = fc.getArgument(_))
      and (result = fc.getTarget().getName() + " string argument")
    )
  }
}

/**
 * A detected definition of PATH_MAX
 */
private int path_max() {
  result = max(Macro macro |
    macro.getName() = "PATH_MAX"
    | macro.getBody().toInt())
}

/**
 * A call to `realpath`. 
 */
class RealpathBW extends BufferWriteCall {
  RealpathBW() {
    exists(path_max()) and // Ignore realpath() calls if PATH_MAX cannot be determined
    getTarget().getQualifiedName() = "realpath"
  }
  
  Expr getDest() { result = getArgument(1) }
  Expr getASource() { result = getArgument(0) }
  
  int getMaxData() {
    result = path_max()
    and this = this // Suppress a compiler warning
  }
}
