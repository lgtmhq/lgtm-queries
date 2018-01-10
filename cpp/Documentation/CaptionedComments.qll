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
 * Provides heuristics to find "todo" and "fixme" comments (in all caps).
 */
import default

string getCommentTextCaptioned(Comment c, string caption) {
    (caption = "TODO" or caption = "FIXME") and
    exists (string commentContents, string commentBody, int offset, string interestingSuffix, int endOfLine, string dontCare, string captionedLine, string followingLine
           | commentContents = c.getContents()
         and commentContents.matches("%" + caption + "%")
         and // Add some '\n's so that any interesting line, and its
             // following line, will definitely begin and end with '\n'.
             commentBody = commentContents.regexpReplaceAll("(?s)^/\\*(.*)\\*/$|^//(.*)$", "\n$1$2\n\n")
         and dontCare = commentBody.regexpFind("\\n[/* \\t\\x0B\\f\\r]*" + caption, _, offset)
         and interestingSuffix = commentBody.suffix(offset)
         and endOfLine = interestingSuffix.indexOf("\n", 1, 0)
         and captionedLine = interestingSuffix.prefix(endOfLine).regexpReplaceAll("^[/*\\s]*" + caption + "\\s*:?", "").trim()
         and followingLine = interestingSuffix.prefix(interestingSuffix.indexOf("\n", 2, 0)).suffix(endOfLine).trim()
         and if captionedLine = ""
             then result = caption + " comment"
             else if followingLine = ""
             then result = caption + " comment: " + captionedLine
             else result = caption + " comment: " + captionedLine + " [...]"
    )
}

