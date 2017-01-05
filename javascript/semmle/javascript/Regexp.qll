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

import Locations
import Expr

/* Regular expression literals are represented as a tree of regular expression terms. */

/** A structure containing a regular expression term, that is, either a regular expression
 * literal or a regular expression term. */
class RegExpParent extends Locatable, @regexpparent {
}

/** A regular expression term, that is, a syntactic part of a regular
 * expression literal. */
abstract class RegExpTerm extends Locatable, @regexpterm {
	/** Get the i-th child term of this term. */
	RegExpTerm getChild(int i) {
		regexpterm(result, _, this, i, _)
	}
	
	/** Get some child term of this term. */
	RegExpTerm getAChild() {
		result = getChild(_)
	}
	
	/** Get the number of child terms of this term. */
	int getNumChild() {
		result = count(getAChild())
	}
	
	/** Get the parent term of this regular expression term, or the
	 * regular expression literal if this is the root term. */
	RegExpParent getParent() {
		regexpterm(this, _, result, _, _)
	}
	
	/** Get the regular expression literal this term belongs to. */
	RegExpLiteral getLiteral() {
		result = getParent+()
	}
	
	string toString() {
		regexpterm(this, _, _, _, result)
	}
	
	/** Can this regular expression term match the empty string? */
	abstract predicate isNullable();
	
	/**
	 * Get the regular expression term that is matched before this one.
	 */
	RegExpTerm getPredecessor() {
		exists (RegExpSequence seq, int i |
			seq.getChild(i) = this and
			seq.getChild(i-1) = result
		) or
		result = ((RegExpTerm)getParent()).getPredecessor()
	}
	
	/**
	 * Get the regular expression term that is matched after this one.
	 */
	RegExpTerm getSuccessor() {
		exists (RegExpSequence seq, int i |
			seq.getChild(i) = this and
			seq.getChild(i+1) = result
		) or
		exists (RegExpTerm parent |
			parent = getParent() and
			not parent instanceof RegExpLookahead |
			result = parent.getSuccessor()
		)
	}
}

/** A quantified regular expression term. */
abstract class RegExpQuantifier extends RegExpTerm, @regexp_quantifier {
	/** Is the quantifier of this term a greedy quantifier? */
	predicate isGreedy() {
		isGreedy(this)
	}
}

/** An escaped regular expression term, that is, a regular expression
 * term starting with a backslash. */
abstract class RegExpEscape extends RegExpTerm, @regexp_escape {
}

/** A constant regular expression term, that is, a regular expression
 * term matching a single string. */
class RegExpConstant extends RegExpTerm, @regexp_constant {
	/** Get the string matched by this constant term. */
	string getValue() {
		regexpConstValue(this, result)
	}

	/**
	 * Whether this constant represents a valid Unicode character (as opposed
	 * to, say, a surrogate code point that does not correspond to a character
	 * by itself.)
	 */
	predicate isCharacter() {
		any()
	}

	predicate isNullable() {
		none()
	}
}

/** A character escape in a regular expression. */
class RegExpCharEscape extends RegExpEscape, RegExpConstant, @regexp_char_escape {
	predicate isCharacter() {
		not (
			// unencodable characters are represented as '?' in the database
			getValue() = "?" and
			exists (string s | s = toString().toLowerCase() |
				// only Unicode escapes give rise to unencodable characters
				s.substring(0, 2) = "\\u" and
				// but '\u003f' actually is the '?' character itself
				s != "\\u003f"
			)
		)
	}
}

/** An alternative term in a regular expression. */
class RegExpAlt extends RegExpTerm, @regexp_alt {
	/** Get one of the alternatives of this term. */
	RegExpTerm getAlternative() {
		result = getAChild()
	}
	
	/** Get the number of alternatives of this term. */
	int getNumAlternative() {
		result = getNumChild()
	}
	
	predicate isNullable() {
		getAlternative().isNullable()
	}
}

/** A sequence term in a regular expression. */
class RegExpSequence extends RegExpTerm, @regexp_seq {
	/** Get an element of this sequence. */
	RegExpTerm getElement() {
		result = getAChild()
	}
	
	/** Get the number of elements in this sequence. */
	int getNumElement() {
		result = getNumChild()
	}
	
	predicate isNullable() {
		forall (RegExpTerm child | child = getAChild() | child.isNullable())
	}
}

/** A caret assertion '^' matching the beginning of a line. */
class RegExpCaret extends RegExpTerm, @regexp_caret {
	predicate isNullable() {
		any()
	}
}

/** A dollar assertion '$' matching the end of a line. */
class RegExpDollar extends RegExpTerm, @regexp_dollar {
	predicate isNullable() {
		any()
	}
}

/** A word boundary assertion '\b'. */
class RegExpWordBoundary extends RegExpTerm, @regexp_wordboundary {
	predicate isNullable() {
		any()
	}
}

/** A non-word boundary assertion '\B'. */
class RegExpNonWordBoundary extends RegExpTerm, @regexp_nonwordboundary {
	predicate isNullable() {
		any()
	}
}

/** A zero-width lookahead assertion. */
abstract class RegExpLookahead extends RegExpTerm {
	/** Get the lookahead term. */
	RegExpTerm getOperand() {
		result = getAChild()
	}

	predicate isNullable() {
		any()
	}
}

/** A positive-lookahead assertion of the form '(?=...)' */
class RegExpPositiveLookahead extends RegExpLookahead, @regexp_positive_lookahead {
}

/** A negative-lookahead assertion of the form '(?!...)' */
class RegExpNegativeLookahead extends RegExpLookahead, @regexp_negative_lookahead {
}

/** A star-quantified term of the form '...*' */
class RegExpStar extends RegExpQuantifier, @regexp_star {
	predicate isNullable() {
		any()
	}
}

/** A plus-quantified term of the form '...+' */
class RegExpPlus extends RegExpQuantifier, @regexp_plus {
	predicate isNullable() {
		getAChild().isNullable()
	}
}

/** An optional term of the form '...?' */
class RegExpOpt extends RegExpQuantifier, @regexp_opt {
	predicate isNullable() {
		any()
	}
}

/** A range-quantified term of the form '...{m,n}' */
class RegExpRange extends RegExpQuantifier, @regexp_range {
	/** Get the lower bound of the range. */
	int getLowerBound() {
		rangeQuantifierLowerBound(this, result)
	}
	
	/** Get the upper bound of the range, if any. */
	int getUpperBound() {
		rangeQuantifierUpperBound(this, result)
	}
	
	predicate isNullable() {
		getAChild().isNullable() or
		getLowerBound() = 0
	}
}

/** A dot regular expression '.' matching any character except end-of-line. */
class RegExpDot extends RegExpTerm, @regexp_dot {
	predicate isNullable() {
		none()
	}
}

/** A grouped regular expression of the form '(...)' or '(?...)' */
class RegExpGroup extends RegExpTerm, @regexp_group {
	/** Is this a capture group? */
	predicate isCapture() {
		isCapture(this, _)
	}
	
	/** If this is a capture group, return its number within the enclosing
	 * regular expression literal. */
	int getNumber() {
		isCapture(this, result)
	}
	
	predicate isNullable() {
		getAChild().isNullable()
	}
}

/** A normal character without special meaning in a regular expression. */
class RegExpNormalChar extends RegExpConstant, @regexp_normal_char {
}

/** A hexadecimal character escape such as '\x0a' in a regular expression. */
class RegExpHexEscape extends RegExpCharEscape, @regexp_hex_escape {
}

/** A unicode character escape such as '\u000a' in a regular expression. */
class RegExpUnicodeEscape extends RegExpCharEscape, @regexp_unicode_escape {
}

/** A decimal character escape such as '\0' in a regular expression. */
class RegExpDecimalEscape extends RegExpCharEscape, @regexp_dec_escape {
}

/** An octal character escape such as '\0177' in a regular expression. */
class RegExpOctalEscape extends RegExpCharEscape, @regexp_oct_escape {
}

/** A control character escape such as '\ca' in a regular expression. */
class RegExpControlEscape extends RegExpCharEscape, @regexp_ctrl_escape {
}

/** A character class escape such as '\w' or '\S' in a regular expression. */
class RegExpCharacterClassEscape extends RegExpEscape, @regexp_char_class_escape {
	/** Get the name of the character class; for example, `w` for `\w`. */
	string getValue() {
		charClassEscape(this, result)
	}
	
	predicate isNullable() {
		none()
	}
}

/** An identity escape such as '\\' or '\/' in a regular expression. */
class RegExpIdentityEscape extends RegExpCharEscape, @regexp_id_escape {
}

/** A back reference of the form '\i' in a regular expression. */
class RegExpBackRef extends RegExpTerm, @regexp_backref {
	/** Get the number of the capture group this back reference refers to. */
	int getNumber() {
		backref(this, result)
	}
	
	/** Get the capture group this back reference refers to. */
	RegExpGroup getGroup() {
		result.getLiteral() = this.getLiteral() and
		result.getNumber() = this.getNumber()
	}
	
	predicate isNullable() {
		getGroup().isNullable()
	}
}

/** A character class in a regular expression. */
class RegExpCharacterClass extends RegExpTerm, @regexp_char_class {
	/** Is this an inverted character class? */
	predicate isInverted() {
		isInverted(this)
	}
	
	predicate isNullable() {
		none()
	}
}

/** A character range in a character class in a regular expression. */
class RegExpCharacterRange extends RegExpTerm, @regexp_char_range {	
	predicate isNullable() {
		none()
	}
}

/** A parse error encountered while processing a regular expression literal. */
class RegExpParseError extends Error, @regexp_parse_error {
	/** The regular expression term that triggered the parse error. */
	RegExpTerm getTerm() {
		regexpParseErrors(this, result, _)
	}
	
	/** The regular expression literal in which the parse error occurred. */
	RegExpLiteral getLiteral() {
		result = getTerm().getLiteral()
	}

	/** A description of the parse error. */
	string getMessage() {
	  regexpParseErrors(this, _, result)
	}

	string toString() {
	  result = getMessage()
	}
}
