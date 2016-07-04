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

import python

predicate format_string(StrConst e) {
	exists(BinaryExpr b | b.getOp() instanceof Mod and b.getLeft() = e)
}

predicate mapping_format(StrConst e) {
	conversion_specifier(e, _).regexpMatch("%\\([A-Z_a-z0-9]+\\).*")
}

/*
MAPPING_KEY = "(\\([^)]+\\))?"
CONVERSION_FLAGS = "[#0\\- +]?"
MINIMUM_FIELD_WIDTH = "(\\*|[0-9]*)"
PRECISION = "(\\.(\\*|[0-9]*))?"
LENGTH_MODIFIER = "[hlL]?"
TYPE = "[diouxXeEfFgGcrs%]"
*/

private
string conversion_specifier_string(StrConst e, int number, int position) {
	exists(string s, string REGEX | s = e.getText() |
		REGEX = "%(\\([^)]*\\))?[#0\\- +]*(\\*|[0-9]*)(\\.(\\*|[0-9]*))?(h|H|l|L)?[diouxXeEfFgGcrs%]" and
		result = s.regexpFind(REGEX, number, position))
}

private
string conversion_specifier(StrConst e, int number) {
	result = conversion_specifier_string(e, number, _) and result != "%%"
}

int illegal_conversion_specifier(StrConst e) {
	format_string(e) and
	"%" = e.getText().charAt(result) and
	// not the start of a conversion specifier or the second % of a %%
	not exists(conversion_specifier_string(e, _, result)) and
	not exists(conversion_specifier_string(e, _, result - 1))
}

/** Gets the number of format items in a format string */
int format_items(StrConst e) {
	result = count(int i | | conversion_specifier(e, i)) +
		// a conversion specifier uses an extra item for each *
		count(int i, int j | conversion_specifier(e, i).charAt(j) = "*")
}

private string str(Expr e) {
    result = ((Num)e).getN()
    or
    result = "'" + ((StrConst)e).getText() + "'"
}

/** Gets a string representation of an expression more suited for embedding in message strings than .toString() */
string repr(Expr e) {
   if exists(str(e)) then
       result = str(e)
   else
       result = e.toString()
}
