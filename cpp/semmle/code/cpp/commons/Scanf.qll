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
 * A library for dealing with scanf-like formatting strings.  This is similar to
 * printf.qll but the format specification for scanf is quite different.
 */
import semmle.code.cpp.Type

/**
 * A scanf-like standard library function.
 */
abstract class ScanfFunction extends Function
{
  abstract int getInputParameterIndex();
  abstract int getFormatParameterIndex();

  predicate isWideCharDefault()
  {
    exists(getName().indexOf("wscanf"))
  }
}

/**
  * The standard function scanf (and variations)
  */
class Scanf extends ScanfFunction
{
  Scanf()
  {
    this instanceof TopLevelFunction and
    (
      hasName("scanf") or                   // scanf(format, args...)
      hasName("wscanf") or                  // wscanf(format, args...)
      hasName("_scanf_l") or                // _scanf_l(format, locale, args...)
      hasName("_wscanf_l")                  // _wscanf_l(format, locale, args...)
    )
  }

  int getInputParameterIndex() { none() }
  int getFormatParameterIndex() { result = 0 }
}

/**
  * The standard function fscanf (and variations)
  */
class Fscanf extends ScanfFunction
{
  Fscanf()
  {
    this instanceof TopLevelFunction and
    (
      hasName("fscanf") or                  // fscanf(src_stream, format, args...)
      hasName("fwscanf") or                 // fwscanf(src_stream, format, args...)
      hasName("_fscanf_l") or               // _fscanf_l(src_stream, format, locale, args...)
      hasName("_fwscanf_l")                 // _fwscanf_l(src_stream, format, locale, args...)
    )
  }

  int getInputParameterIndex() { result = 0 }
  int getFormatParameterIndex() { result = 1 }
}

/**
  * The standard function sscanf (and variations)
  */
class Sscanf extends ScanfFunction
{
  Sscanf()
  {
    this instanceof TopLevelFunction and
    (
      hasName("sscanf") or                  // sscanf(src_stream, format, args...)
      hasName("swscanf") or                 // swscanf(src, format, args...)
      hasName("_sscanf_l") or               // _sscanf_l(src, format, locale, args...)
      hasName("_swscanf_l")                 // _swscanf_l(src, format, locale, args...)
    )
  }

  int getInputParameterIndex() { result = 0 }
  int getFormatParameterIndex() { result = 1 }
}

/**
  * The standard(ish) function snscanf (and variations)
  */
class Snscanf extends ScanfFunction
{
  Snscanf()
  {
    this instanceof TopLevelFunction and
    (
      hasName("_snscanf") or                // _snscanf(src, max_amount, format, args...)
      hasName("_snwscanf")                  // _snwscanf(src, max_amount, format, args...)
          // note that the max_amount is not a limit on the output length, it's an input length
          // limit used with non null-terminated strings.
    )
  }

  int getInputParameterIndex() { result = 0 }
  int getFormatParameterIndex() { result = 2 }
}

/**
 * A call to one of the scanf functions.
 */
class ScanfFunctionCall extends FunctionCall
{
  ScanfFunctionCall()
  {
    this.getTarget() instanceof ScanfFunction
  }

  ScanfFunction getScanfFunction()
  {
    result = getTarget()
  }

  /** the index at which the input string or stream occurs in the argument list */
  int getInputParameterIndex()
  {
    result = getScanfFunction().getInputParameterIndex()
  }

  /** the index at which the format string occurs in the argument list */
  int getFormatParameterIndex()
  {
    result = getScanfFunction().getFormatParameterIndex()
  }

  /** the format expression used in this call */
  Expr getFormat()
  {
    result = this.getArgument(this.getFormatParameterIndex())
  }

  /** Whether the default meaning of %s is a wchar_t* or a char*. */
  predicate isWideCharDefault()
  {
    getScanfFunction().isWideCharDefault()
  }
}

/**
 * A class to represent format strings that occur as arguments to invocations of scanf functions.
 */
class ScanfFormatLiteral extends Expr {
  ScanfFormatLiteral() {
    exists(ScanfFunctionCall sfc | sfc.getFormat() = this) and
    this.isConstant()
  }

  /** the function call where this format string is used */
  ScanfFunctionCall getUse() {
    result.getFormat() = this
  }

  /** Whether the default meaning of %s is a wchar_t* or a char*. */
  predicate isWideCharDefault() {
    getUse().getTarget().(ScanfFunction).isWideCharDefault()
  }

  /** the format string itself; we perform transformations
      '%%' is replaced with '_'
        (avoids accidentally processing them as format specifiers)
      '%*' is replaced with '_'
        (%*any is matched but not assigned to an argument)
  */
  string getFormat() {
    result = this.getValue().replaceAll("%%", "_").replaceAll("%*", "_")
  }

  /** the number of conversion specifiers (not counting %% and %*...) */
  int getNumConvSpec() {
    result = count(this.getFormat().indexOf("%"))
  }

  /** the position in the string at which the nth conversion specifier starts */
  int getConvSpecOffset(int n) {
       n = 0 and result = this.getFormat().indexOf("%", 0, 0)
    or n > 0 and exists(int p | n = p + 1 and result = this.getFormat().indexOf("%", 0, this.getConvSpecOffset(p) + 2))
  }

  /** regular expressions to match the individual parts of a conversion specifier */
  string getMaxWidthRegexp() { result = "(?:[1-9][0-9]*)?" }
  string getLengthRegexp() { result = "(?:hh?|ll?|L|q|j|z|t)?" }
  string getConvCharRegexp() { result = "[aAcCdeEfFgGimnopsSuxX]" }

  /** the regular expression used for matching a whole conversion specifier */
  string getConvSpecRegexp() {
    // capture groups: 1 - entire conversion spec, including "%"
    //                 2 - maximum width
    //                 3 - length modifier
    //                 4 - conversion character
    result = "(\\%("+this.getMaxWidthRegexp()+")("+this.getLengthRegexp()+")("+this.getConvCharRegexp()+")).*"
  }

  /** parse a conversion specifier
    *  @param n     which conversion specifier to parse
    *  @param spec  the whole conversion specifier
    *  @param width the maximum width option of this input (empty string if none is given)
    *  @param len   the length flag of this input (empty string if none is given)
    *  @param conv  the conversion character of this input */
  predicate parseConvSpec(int n, string spec, string width, string len, string conv) {
    exists(int offset, string fmt, string rst, string regexp |
      offset = this.getConvSpecOffset(n) and
      fmt = this.getFormat() and
      rst = fmt.substring(offset, fmt.length()) and
      regexp = this.getConvSpecRegexp() and (
        spec  = rst.regexpCapture(regexp, 1) and
        width = rst.regexpCapture(regexp, 2) and
        len   = rst.regexpCapture(regexp, 3) and
        conv  = rst.regexpCapture(regexp, 4)
      )
    )
  }

  /** the maximum width option of the nth input (empty string if none is given) */
  string getMaxWidthOpt(int n) { exists(string spec, string len, string conv | this.parseConvSpec(n, spec, result, len, conv)) }

  /** the maximum width of the nth input */
  int getMaxWidth(int n) { result = this.getMaxWidthOpt(n).toInt() }

  /** the length flag of the nth conversion specifier */
  string getLength(int n) { exists(string spec, string width, string conv | this.parseConvSpec(n, spec, width, result, conv)) }

  /** the conversion character of the nth conversion specifier */
  string getConversionChar(int n) { exists(string spec, string width, string len | this.parseConvSpec(n, spec, width, len, result)) }

  /** the maximum length of the string that can be produced by the nth conversion specifier of this format string;
      fails if no estimate is possible (or implemented)  */
  int getMaxConvertedLength(int n) {
    (this.getConversionChar(n).toLowerCase() = "s") and
    (result = this.getMaxWidth(n))
  }
}