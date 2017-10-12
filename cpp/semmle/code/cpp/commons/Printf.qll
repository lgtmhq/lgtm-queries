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
 * A library for dealing with printf-like formatting strings.
 */
import semmle.code.cpp.Type
import semmle.code.cpp.commons.CommonType
import semmle.code.cpp.commons.StringAnalysis

/**
 * A standard library function that uses a printf-like formatting string.
 */
abstract class FormattingFunction extends Function {
  /** the position at which the format parameter occurs */
  abstract int getFormatParameterIndex();

  /** Whether the default meaning of %s is a wchar_t* or a char*. Either
   *  way, %S will have the opposite meaning. */
  predicate isWideCharDefault() { none() }

  /** the position at which the output parameter, if any, occurs */
  int getOutputParameterIndex() { none() }
}

/**
 * The standard functions printf, wprintf and their glib variants.
 */
class Printf extends FormattingFunction {
  Printf() { this instanceof TopLevelFunction and (hasGlobalName("printf") or hasGlobalName("wprintf") or hasGlobalName("g_printf")) }

  int getFormatParameterIndex() { result=0 }
  predicate isWideCharDefault() { hasGlobalName("wprintf") }
}

/**
 * The standard functions fprintf, fwprintf and their glib variants.
 */
class Fprintf extends FormattingFunction {
  Fprintf() { this instanceof TopLevelFunction and (hasGlobalName("fprintf") or hasGlobalName("fwprintf") or hasGlobalName("g_fprintf"))}

  int getFormatParameterIndex() { result=1 }
  predicate isWideCharDefault() { hasGlobalName("fwprintf") }
  int getOutputParameterIndex() { result=0 }
}

/**
 * The standard function sprintf and its glib variants.
 */
class Sprintf extends FormattingFunction {
  Sprintf() { this instanceof TopLevelFunction and (hasGlobalName("sprintf") or hasGlobalName("g_strdup_printf") or hasGlobalName("g_sprintf")) }

  /** the position at which the format parameter occurs */
  int getFormatParameterIndex() {
    if hasGlobalName("g_strdup_printf") then result = 0 else result = 1
  }
  int getOutputParameterIndex() {
    not hasGlobalName("g_strdup_printf") and result = 0
  }
}

/**
 * The standard functions snprintf and swprintf, and their
 * Microsoft and glib variants.
 */
class Snprintf extends FormattingFunction {
  Snprintf() {
    this instanceof TopLevelFunction and (
      hasGlobalName("snprintf") // C99 defines snprintf
      or hasGlobalName("swprintf") // The s version of wide-char printf is also always the n version
      // Microsoft has _snprintf as well as several other variations
      or hasGlobalName("_snprintf")
      or hasGlobalName("_snprintf_l")
      or hasGlobalName("_snwprintf")
      or hasGlobalName("_snwprintf_l")
      or hasGlobalName("_sprintf_s_l")
      or hasGlobalName("_swprintf_s_l")
      or hasGlobalName("g_snprintf")
    )
  }

  int getFormatParameterIndex() {
    if getName().matches("%\\_l")
      then result = getNumberOfParameters() - 2
      else result = getNumberOfParameters() - 1
  }

  predicate isWideCharDefault() { getName().matches("%w%") }
  int getOutputParameterIndex() { result=0 }
}

/**
 * The standard function syslog.
 */
class Syslog extends FormattingFunction {
  Syslog() {
    this instanceof TopLevelFunction and (
      hasGlobalName("syslog")
    )
  }

  /** the position at which the format parameter occurs */
  int getFormatParameterIndex() { result=1 }
}

predicate primitiveVariadicFormatter(TopLevelFunction f, int formatParamIndex, boolean wide) {
  f.getName().regexpMatch("_?_?va?[fs]?n?w?printf(_s)?(_p)?(_l)?")
  and (
    if f.getName().matches("%\\_l")
    then formatParamIndex = f.getNumberOfParameters() - 3
    else formatParamIndex = f.getNumberOfParameters() - 2
  ) and if f.getName().matches("%w%") then wide = true else wide = false
}

private
predicate callsVariadicFormatter(Function f, int formatParamIndex, boolean wide) {
  exists(FunctionCall fc, int i |
    variadicFormatter(fc.getTarget(), i, wide)
    and fc.getEnclosingFunction() = f
    and fc.getArgument(i) = f.getParameter(formatParamIndex).getAnAccess()
  )
}

predicate variadicFormatter(Function f, int formatParamIndex, boolean wide) {
  primitiveVariadicFormatter(f, formatParamIndex, wide)
  or (
    not f.isVarargs()
    and callsVariadicFormatter(f, formatParamIndex, wide)
  )
}

/**
 * A function not in the standard library which takes a printf-style formatting
 * string and a variable number of arguments.
 */
class UserDefinedFormattingFunction extends FormattingFunction {
  UserDefinedFormattingFunction() {
    isVarargs() and callsVariadicFormatter(this, _, _)
  }

  /** the position at which the format parameter occurs */
  int getFormatParameterIndex() { callsVariadicFormatter(this, result, _) }

  predicate isWideCharDefault() { callsVariadicFormatter(this, _, true) }
}

/**
 * The Objective C method stringWithFormat:.
 */
class NsstringStringWithFormat extends FormattingFunction {
  NsstringStringWithFormat() {
    getQualifiedName().matches("NSString%::+stringWithFormat:") or
    getQualifiedName().matches("NSString%::+localizedStringWithFormat:")
  }

  int getFormatParameterIndex() {
    result = 0
  }
}

/**
 * A call to one of the formatting functions.
 */
class FormattingFunctionCall extends Expr {
  FormattingFunctionCall() {
    this.(Call).getTarget() instanceof FormattingFunction
  }

  /**
   * Get the formatting function being called.
   */
  Function getTarget() {
    result = this.(Call).getTarget()
  }

  /**
   * Get the `i`th argument for this call.
   *
   * The range of `i` is from `0` to `getNumberOfArguments() - 1`.
   */
  Expr getArgument(int i) {
    result = this.(Call).getArgument(i)
  }

  /**
   * Get the number of actual parameters in this call; use
   * `getArgument(i)` with `i` between `0` and `result - 1` to
   * retrieve actuals.
   */
  int getNumberOfArguments() {
    result = this.(Call).getNumberOfArguments()
  }

  /** the index at which the format string occurs in the argument list */
  int getFormatParameterIndex() {
    result = this.getTarget().(FormattingFunction).getFormatParameterIndex()
  }

  /** the format expression used in this call */
  Expr getFormat() {
    result = this.getArgument(this.getFormatParameterIndex())
  }

  /** the nth argument to the format (including width and precision arguments) */
  Expr getFormatArgument(int n) {
    exists(int i |
      result = this.getArgument(i)
      and n >= 0
      and n = i - getTarget().getNumberOfParameters()
    )
  }

  /** the argument corresponding to the nth conversion specifier */
  Expr getConversionArgument(int n) {
    exists(FormatLiteral fl, int b, int o |
      fl = this.getFormat() and
      b = sum(int i, int toSum | (i < n) and (toSum = fl.getNumArgNeeded(i)) | toSum) and
      o = fl.getNumArgNeeded(n) and
      o > 0 and
      result = this.getFormatArgument(b+o-1))
  }

  /** the argument corresponding to the nth conversion specifier's minimum field width
      (fails if that conversion specifier has an explicit minimum field width) */
  Expr getMinFieldWidthArgument(int n) {
    exists(FormatLiteral fl, int b |
      fl = this.getFormat() and
      b = sum(int i, int toSum | (i < n) and (toSum = fl.getNumArgNeeded(i)) | toSum) and
      fl.hasImplicitMinFieldWidth(n) and
      result = this.getFormatArgument(b))
  }

  /** the argument corresponding to the nth conversion specifier's precision
      (fails if that conversion specifier has an explicit precision) */
  Expr getPrecisionArgument(int n) {
    exists(FormatLiteral fl, int b, int o |
      fl = this.getFormat() and
      b = sum(int i, int toSum | (i < n) and (toSum = fl.getNumArgNeeded(i)) | toSum) and
      (if fl.hasImplicitMinFieldWidth(n) then o=1 else o=0) and
      fl.hasImplicitPrecision(n) and
      result = this.getFormatArgument(b+o))
  }

  /** the number of arguments to this call that are parameters to the format string */
  int getNumFormatArgument() {
    result = count(this.getFormatArgument(_))
  }
}

/**
 * A class to represent format strings that occur as arguments to invocations of formatting functions.
 */
class FormatLiteral extends Expr {
  FormatLiteral() {
    exists(FormattingFunctionCall ffc | ffc.getFormat() = this) and
    this.isConstant()
  }

  /** the function call whether this format string is used */
  FormattingFunctionCall getUse() {
    result.getFormat() = this
  }

  predicate isWideCharDefault() {
    getUse().getTarget().(FormattingFunction).isWideCharDefault()
  }

  /** the format string, with '%%' replaced by '_'
      (to avoid processing '%%' as a format specifier)
  */
  string getFormat() {
    result = this.getValue().replaceAll("%%", "_")
  }

  /** the number of conversion specifiers (not counting %%) */
  int getNumConvSpec() {
    result = count(this.getFormat().indexOf("%"))
  }

  /** the position in the string at which the nth conversion specifier starts */
  int getConvSpecOffset(int n) {
       n = 0 and result = this.getFormat().indexOf("%", 0, 0)
    or n > 0 and exists(int p | n = p + 1 and result = this.getFormat().indexOf("%", 0, this.getConvSpecOffset(p)+2))
  }

  /** regular expressions to match the individual parts of a conversion specifier */
  string getFlagRegexp() { result = "[-+ #0'I]*" }
  string getFieldWidthRegexp() { result = "(?:[1-9][0-9]*|\\*|\\*[0-9]+\\$)?" }
  string getPrecRegexp() { result = "(?:\\.(?:[0-9]*|\\*|\\*[0-9]+\\$))?" }
  string getLengthRegexp() { result = "(?:hh?|ll?|L|q|j|z|t)?" }
  string getConvCharRegexp() { result = "[aAcCdeEfFgGimnopsSuxX@]" }

  /** the regular expression used for matching a whole conversion specifier */
  string getConvSpecRegexp() {
    // capture groups: 1 - entire conversion spec, including "%"
    //                 2 - flags
    //                 3 - minimum field width
    //                 4 - precision
    //                 5 - length
    //                 6 - conversion character
    // NB: this matches "%%" with conversion character "%"
    result = "(?s)(\\%("+this.getFlagRegexp()+")("+this.getFieldWidthRegexp()+")("+this.getPrecRegexp()+")("+this.getLengthRegexp()+")("+this.getConvCharRegexp()+")"+
                 "|\\%\\%).*"
  }

  /** parse a conversion specifier
    *  @param n which conversion specifier to parse
    *  @param spec the whole conversion specifier
    *  @param flags the flags of the conversion specifier (empty string if none are given)
    *  @param width the minimum field width of the conversion specifier (empty string if none is given)
    *  @param prec the precision of the conversion specifier (empty string if none is given)
    *  @param len the length flag of the conversion specifier (empty string if none is given)
    *  @param conv the conversion character of the conversion specifier ("%" for specifier "%%") */
  predicate parseConvSpec(int n, string spec, string flags, string width, string prec, string len, string conv) {
    exists(int offset, string fmt, string rst, string regexp |
      offset = this.getConvSpecOffset(n) and
      fmt = this.getFormat() and
      rst = fmt.substring(offset, fmt.length()) and
      regexp = this.getConvSpecRegexp() and
        ((spec  = rst.regexpCapture(regexp, 1) and
         flags = rst.regexpCapture(regexp, 2) and
         width = rst.regexpCapture(regexp, 3) and
         prec  = rst.regexpCapture(regexp, 4) and
         len   = rst.regexpCapture(regexp, 5) and
         conv  = rst.regexpCapture(regexp, 6))
         or
         (spec = rst.regexpCapture(regexp, 1) and
          not exists(rst.regexpCapture(regexp, 2)) and
          flags = "" and
          width = "" and
          prec = "" and
          len = "" and
          conv = "%")))
  }

  /** the nth conversion specifier (including the initial %) */
  string getConvSpec(int n) {
    exists(int offset, string fmt, string rst, string regexp |
      offset = this.getConvSpecOffset(n) and
      fmt = this.getFormat() and
      rst = fmt.substring(offset, fmt.length()) and
      regexp = this.getConvSpecRegexp() and
      result  = rst.regexpCapture(regexp, 1))
  }

  /** the flags of the nth conversion specifier */
  string getFlags(int n) {
    exists(string spec, string width, string prec, string len, string conv | this.parseConvSpec(n, spec, result, width, prec, len, conv))
  }

  /** whether the nth conversion specifier has alternate flag ("#") */
  predicate hasAlternateFlag(int n) { this.getFlags(n).matches("%#%") }

  /** whether the nth conversion specifier has zero padding flag ("0") */
  predicate isZeroPadded(int n) { this.getFlags(n).matches("%0%") and not this.isLeftAdjusted(n) }

  /** whether the nth conversion specifier has flag left adjustment flag ("-")
    * note that this overrides the zero padding flag */
  predicate isLeftAdjusted(int n) { this.getFlags(n).matches("%-%") }

  /** whether the nth conversion specifier has the blank flag (" ") */
  predicate hasBlank(int n) { this.getFlags(n).matches("% %") }

  /** whether the nth conversion specifier has the explicit sign flag ("+") */
  predicate hasSign(int n) { this.getFlags(n).matches("%+%") }

  /** whether the nth conversion specifier has the thousands grouping flag ("'") */
  predicate hasThousandsGrouping(int n) { this.getFlags(n).matches("%'%") }

  /** whether the nth conversion specifier has the alternative digits flag ("I") */
  predicate hasAlternativeDigits(int n) { this.getFlags(n).matches("%I%") }

  /** the minimum field width of the nth conversion specifier (empty string if none is given) */
  string getMinFieldWidthOpt(int n) { exists(string spec, string flags, string prec, string len, string conv | this.parseConvSpec(n, spec, flags, result, prec, len, conv)) }

  /** whether the nth conversion specifier has a minimum field width */
  predicate hasMinFieldWidth(int n) { this.getMinFieldWidthOpt(n) != "" }

  /** whether the nth conversion specifier has an explicitly given minimum field width */
  predicate hasExplicitMinFieldWidth(int n) { this.getMinFieldWidthOpt(n).regexpMatch("[0-9]+") }

  /** whether the nth conversion specifier has an implicitly given minimum field width (either "*" or "*i$" for some number i) */
  predicate hasImplicitMinFieldWidth(int n) { this.getMinFieldWidthOpt(n).regexpMatch("\\*.*") }

  /** the minimum field width of the nth conversion specifier */
  int getMinFieldWidth(int n) { result = this.getMinFieldWidthOpt(n).toInt() }

  /** the precision of the nth conversion specifier (empty string if none is given) */
  string getPrecisionOpt(int n) { exists(string spec, string flags, string width, string len, string conv | this.parseConvSpec(n, spec, flags, width, result, len, conv)) }

  /** whether the nth conversion specifier has a precision */
  predicate hasPrecision(int n) { this.getPrecisionOpt(n) != "" }

   /** whether the nth conversion specifier has an explicitly given precision */
  predicate hasExplicitPrecision(int n) { this.getPrecisionOpt(n).regexpMatch("\\.[0-9]*") }

  /** whether the nth conversion specifier has an implicitly given precision (either "*" or "*i$" for some number i) */
  predicate hasImplicitPrecision(int n) { this.getPrecisionOpt(n).regexpMatch("\\.\\*.*") }

  /** the precision of the nth conversion specifier */
  int getPrecision(int n) {
    if this.getPrecisionOpt(n) = "." then
      result = 0
    else
      result = this.getPrecisionOpt(n).regexpCapture("\\.([0-9]*)", 1).toInt()
  }

  /** the length flag of the nth conversion specifier */
  string getLength(int n) { exists(string spec, string flags, string width, string prec, string conv | this.parseConvSpec(n, spec, flags, width, prec, result, conv)) }

  /** the conversion character of the nth conversion specifier */
  string getConversionChar(int n) { exists(string spec, string flags, string width, string prec, string len | this.parseConvSpec(n, spec, flags, width, prec, len, result)) }

  int targetBitSize() { result = this.getFullyConverted().getType().getSize() }

  LongType getLongType() {
         if this.targetBitSize() = 4 then result.getSize() = min(LongType l | | l.getSize())
    else if this.targetBitSize() = 8 then result.getSize() = max(LongType l | | l.getSize())
    else any()
  }

  Intmax_t getIntmax_t() {
         if this.targetBitSize() = 4 then result.getSize() = min(Intmax_t l | | l.getSize())
    else if this.targetBitSize() = 8 then result.getSize() = max(Intmax_t l | | l.getSize())
    else any()
  }

  Size_t getSize_t() {
         if this.targetBitSize() = 4 then result.getSize() = min(Size_t l | | l.getSize())
    else if this.targetBitSize() = 8 then result.getSize() = max(Size_t l | | l.getSize())
    else any()
  }

  Ptrdiff_t getPtrdiff_t() {
         if this.targetBitSize() = 4 then result.getSize() = min(Ptrdiff_t l | | l.getSize())
    else if this.targetBitSize() = 8 then result.getSize() = max(Ptrdiff_t l | | l.getSize())
    else any()
  }

  /** the family of integral types required by the nth conversion specifier's length flag */
  IntegralType getIntegralConversion(int n) {
    exists(string len | len = this.getLength(n) and
        ((len="hh" and result instanceof IntType)
      or (len="h" and result instanceof IntType)
      or (len="l" and result = this.getLongType())
      or ((len="ll" or len="q")
                  and result instanceof LongLongType)
      or (len="L" and result instanceof IntType)  // doesn't affect integral conversion
      or (len="j" and result = this.getIntmax_t())
      or ((len="z" or len="Z")
                  and result = this.getSize_t())
      or (len="t" and result = this.getPtrdiff_t())
      or (len=""  and result instanceof IntType)))
  }

  /** the family of integral types output / displayed by the nth conversion specifier's length flag */
  IntegralType getIntegralDisplayType(int n) {
    exists(string len | len = this.getLength(n) and
        ((len="hh" and result instanceof CharType)
      or (len="h" and result instanceof ShortType)
      or (len="l" and result = this.getLongType())
      or ((len="ll" or len="q")
                  and result instanceof LongLongType)
      or (len="L" and result instanceof IntType)  // doesn't affect integral conversion
      or (len="j" and result = this.getIntmax_t())
      or ((len="z" or len="Z")
                  and result = this.getSize_t())
      or (len="t" and result = this.getPtrdiff_t())
      or (len=""  and result instanceof IntType)))
  }

  /** the family of floating point types required by the nth conversion specifier's length flag */
  FloatingPointType getFloatingPointConversion(int n) {
    exists(string len | len = this.getLength(n) and
      if len="L" then
        result instanceof LongDoubleType
      else
        result instanceof DoubleType)
  }

  /** the family of pointer types required by the nth conversion specifier's length flag */
  PointerType getStorePointerConversion(int n) {
    exists(IntegralType base |
      exists(string len | len = this.getLength(n) |
           (len="hh" and base instanceof CharType)
        or (len="h"  and base instanceof ShortType)
        or (len="l"  and base = this.getLongType())
        or (len="ll" and base instanceof LongLongType)
        or (len="q" and base instanceof LongLongType)
      )
      and base.isSigned() and base = result.getBaseType()
    )
  }

  /** the argument type required by the nth conversion specifier */
  Type getConversionType(int n) {
    result = getConversionType1(n) or
    result = getConversionType2(n) or
    result = getConversionType3(n) or
    result = getConversionType4(n) or
    result = getConversionType5(n) or
    result = getConversionType6(n) or
    result = getConversionType7(n) or
    result = getConversionType8(n)
  }

  private Type getConversionType1(int n) {
    exists(string cnv | cnv = this.getConversionChar(n) |
      cnv.regexpMatch("c|C|d|i") and result = this.getIntegralConversion(n)
      and not result.(IntegralType).isExplicitlySigned()
      and not result.(IntegralType).isExplicitlyUnsigned()
    )
  }

  private Type getConversionType2(int n) {
    exists(string cnv | cnv = this.getConversionChar(n) |
      cnv.regexpMatch("o|u|x|X") and result = this.getIntegralConversion(n) and result.(IntegralType).isUnsigned()
    )
  }

  private Type getConversionType3(int n) {
    exists(string cnv | cnv = this.getConversionChar(n) |
      cnv.regexpMatch("a|A|e|E|f|F|g|G") and result = this.getFloatingPointConversion(n)
    )
  }

  private string getEffectiveStringConversionChar(int n) {
    exists(string len, string conv | this.parseConvSpec(n, _, _, _, _, len, conv) and (conv = "s" or conv = "S") |
      (len = "l" and result = "S") or
      (len = "h" and result = "s") or
      (len != "l" and len != "h" and (result = "s" or result = "S") and (if isWideCharDefault() then result != conv else result = conv))
    )
  }

  private Type getConversionType4(int n) {
    exists(string cnv, CharType t | cnv = this.getEffectiveStringConversionChar(n) |
      cnv="s" and t = result.(PointerType).getBaseType()
      and not t.isExplicitlySigned()
      and not t.isExplicitlyUnsigned()
    )
  }

  private Type getConversionType5(int n) {
    exists(string cnv | cnv = this.getEffectiveStringConversionChar(n) |
      cnv="S" and exists(Wchar_t wch | wch = result.(PointerType).getBaseType() and wch.isConst())
    )
  }

  private Type getConversionType6(int n) {
    exists(string cnv | cnv = this.getConversionChar(n) |
      cnv="p" and result instanceof VoidPointerType
    )
  }

  private Type getConversionType7(int n) {
    exists(string cnv | cnv = this.getConversionChar(n) |
      cnv="n" and result = this.getStorePointerConversion(n)
    )
  }

  private Type getConversionType8(int n) {
    exists(string cnv | cnv = this.getConversionChar(n) |
      cnv="n" and not exists(this.getStorePointerConversion(n)) and result instanceof IntPointerType
    )
  }

  /** the number of arguments required by the nth conversion specifier of this format string */
  int getNumArgNeeded(int n) {
    this.getConversionChar(n)!="%" and
    exists(int n1, int n2, int n3 |
      (if this.hasImplicitMinFieldWidth(n) then n1=1 else n1=0) and
      (if this.hasImplicitPrecision(n) then n2=1 else n2=0) and
      (if this.getConversionChar(n)="m" then n3=0 else n3=1) and
      result = n1 + n2 + n3)
  }

  /** the number of arguments needed by this format string */
  int getNumArgNeeded() {
    result = sum(int n, int toSum | (toSum = this.getNumArgNeeded(n)) | toSum)
  }

  predicate specsAreKnown() {
    this.getNumConvSpec() = count(int n | exists(this.getNumArgNeeded(n)))
  }

  /** the maximum length of the string that can be produced by the nth conversion specifier of this format string;
      fails if no estimate is possible (or implemented)  */
  int getMaxConvertedLength(int n) {
    exists(int len |
      (if this.hasExplicitMinFieldWidth(n) then
        result = len.maximum(this.getMinFieldWidth(n))
      else
        not this.hasImplicitMinFieldWidth(n) and result = len)
      and
      (this.getConversionChar(n)="%" and
         len = 1
      or this.getConversionChar(n).toLowerCase()="c" and
         this.getLength(n)="" and len = 1 // e.g. 'a'
      or this.getConversionChar(n).toLowerCase()="f" and
         exists(int dot, int afterdot |
           (if this.getPrecision(n) = 0 then dot = 0 else dot = 1)
           and
           (if this.hasExplicitPrecision(n) then
             afterdot = this.getPrecision(n)
            else
             not this.hasImplicitPrecision(n) and afterdot = 6)
           and
             len = 1 + 309 + dot + afterdot) // e.g. -1e308="-100000"...
      or this.getConversionChar(n).toLowerCase()="e" and
         exists(int dot, int afterdot |
           (if this.getPrecision(n) = 0 then dot = 0 else dot = 1)
           and
           (if this.hasExplicitPrecision(n) then
             afterdot = this.getPrecision(n)
            else
             not this.hasImplicitPrecision(n) and afterdot = 6)
           and
             len = 1 + 1 + dot + afterdot + 1 + 1 + 3) // -1e308="-1.000000e+308"
      or this.getConversionChar(n).toLowerCase()="g" and
         exists(int dot, int afterdot |
           (if this.getPrecision(n) = 0 then dot = 0 else dot = 1)
           and
           (if this.hasExplicitPrecision(n) then
             afterdot = this.getPrecision(n)
            else
             not this.hasImplicitPrecision(n) and afterdot = 6)
           and
             // note: this could be displayed in the style %e or %f;
             //       however %f is only used when 'P > X >= -4'
             //         where P is the precision (default 6, minimum 1)
             //         and X is the exponent
             //         using a precision of P - 1 - X (i.e. to P significant figures)
             //       in other words the number is displayed to P significant figures if that is enough to express
             //       it with no trailing zeroes and at most four leading zeroes beyond the significant figures
             //       (e.g. 123456, 0.000123456 are just OK)
             //       so case %f can be at most P characters + 4 zeroes, sign, dot = P + 6
             len = (afterdot.maximum(1) + 6).maximum(1 + 1 + dot + afterdot + 1 + 1 + 3)) // (e.g. "-1.59203e-319")
      or (this.getConversionChar(n).toLowerCase()="d" or this.getConversionChar(n).toLowerCase()="i") and
        // e.g. -2^31 = "-2147483648"
        exists(int sizeBits |
          sizeBits = min(int bits |
            bits = getIntegralDisplayType(n).getSize() * 8 or
            exists(IntegralType t | t = getUse().getConversionArgument(n).getType().getUnderlyingType() | t.isSigned() and bits = t.getSize() * 8)
          ) and
          len = 1 + ((sizeBits - 1) / 10.0.log2()).ceil()
            // this calculation is as %u (below) only we take out the sign bit (- 1) and allow a whole
            // character for it to be expressed as '-'.
        )
      or this.getConversionChar(n).toLowerCase()="u" and
        // e.g. 2^32 - 1 = "4294967295"
        exists(int sizeBits |
          sizeBits = min(int bits |
            bits = getIntegralDisplayType(n).getSize() * 8 or
            exists(IntegralType t | t = getUse().getConversionArgument(n).getType().getUnderlyingType() | t.isUnsigned() and bits = t.getSize() * 8)
          ) and
          len = (sizeBits / 10.0.log2()).ceil()
            // convert the size from bits to decimal characters, and round up as you can't have
            // fractional characters (10.0.log2() is the number of bits expressed per decimal character)
        )
      or this.getConversionChar(n).toLowerCase()="x" and
        // e.g. "12345678"
        exists(int sizeBytes, int baseLen |
          sizeBytes = min(int bytes |
            bytes = getIntegralDisplayType(n).getSize() or
            exists(IntegralType t | t = getUse().getConversionArgument(n).getType().getUnderlyingType() | t.isUnsigned() and bytes = t.getSize())
          ) and (
            baseLen = sizeBytes * 2
          ) and (
            if hasAlternateFlag(n) then len = 2 + baseLen else len = baseLen // "0x"
          )
        )
      or this.getConversionChar(n).toLowerCase()="p" and
        exists(PointerType ptrType, int baseLen | (
            ptrType = getFullyConverted().getType()
          ) and (
            baseLen = max(ptrType.getSize() * 2) // e.g. "0x1234567812345678"; exact format is platform dependent
          ) and (
            if hasAlternateFlag(n) then len = 2 + baseLen else len = baseLen // "0x"
          )
        )
      or this.getConversionChar(n).toLowerCase()="o" and
        // e.g. 2^32 - 1 = "37777777777"
        exists(int sizeBits, int baseLen |
          sizeBits = min(int bits |
            bits = getIntegralDisplayType(n).getSize() * 8 or
            exists(IntegralType t | t = getUse().getConversionArgument(n).getType().getUnderlyingType() | t.isUnsigned() and bits = t.getSize() * 8)
          ) and (
            baseLen = (sizeBits / 3.0).ceil()
          ) and (
            if hasAlternateFlag(n) then len = 1 + baseLen else len = baseLen // "0"
          )
        )
      or this.getConversionChar(n).toLowerCase()="s" and
         len = min(int v |
           (v = this.getPrecision(n)) or
           (v = this.getUse().getFormatArgument(n).(AnalysedString).getMaxLength() - 1) // (don't count null terminator)
         )
      )
    )
  }

  /** as getMaxConvertedLength, except that float to string conversions are assumed to be 8 bytes.  This is helpful
      for determining whether a buffer overflow is caused by long float to string conversions. */
  int getMaxConvertedLengthLimited(int n) {
    if this.getConversionChar(n).toLowerCase() = "f" then (
      result = getMaxConvertedLength(n).minimum(8)
    ) else (
      result = getMaxConvertedLength(n)
    )
  }

  /** the constant part of the format string just before the nth conversion specifier
      if n is zero, this will be the constant prefix before the 0th specifier, otherwise it is the string between
      the end of the n-1th specifier and the nth specifier
      fails if n is negative or not strictly less than the number of conversion specifiers */
  string getConstantPart(int n) {
    if n=0 then
      result = this.getFormat().substring(0, this.getConvSpecOffset(0))
    else
      result = this.getFormat().substring(this.getConvSpecOffset(n-1)+this.getConvSpec(n-1).length(), this.getConvSpecOffset(n))
  }

  /** the constant part of the format string after the last conversion specifier */
  string getConstantSuffix() {
    exists(int n | n = this.getNumConvSpec() and
      (if n > 0 then
        result = this.getFormat().substring(this.getConvSpecOffset(n-1)+this.getConvSpec(n-1).length(), this.getFormat().length())
       else
        result = this.getFormat()))
  }

  int getMaxConvertedLengthAfter(int n) {
    if n=this.getNumConvSpec() then
      result = this.getConstantSuffix().length() + 1
    else
      result = this.getConstantPart(n).length()+this.getMaxConvertedLength(n)+this.getMaxConvertedLengthAfter(n+1)
  }

  int getMaxConvertedLengthAfterLimited(int n) {
    if n=this.getNumConvSpec() then
      result = this.getConstantSuffix().length() + 1
    else
      result = this.getConstantPart(n).length()+this.getMaxConvertedLengthLimited(n)+this.getMaxConvertedLengthAfterLimited(n+1)
  }

  int getMaxConvertedLength() {
    result = this.getMaxConvertedLengthAfter(0)
  }
}
