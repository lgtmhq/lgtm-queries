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
 * Provides classes for detecting generated code.
 */

import javascript
import semmle.javascript.frameworks.Bundling
import semmle.javascript.frameworks.Emscripten
import semmle.javascript.frameworks.GWT
import semmle.javascript.SourceMaps

/**
 * A comment that marks generated code.
 */
abstract class GeneratedCodeMarkerComment extends Comment {
}

/**
 * A source mapping comment, viewed as a marker comment indicating generated code.
 */
private class SourceMappingCommentMarkerComment extends GeneratedCodeMarkerComment {
  SourceMappingCommentMarkerComment() {
    this instanceof SourceMappingComment
  }
}

/**
 * A marker comment left by a specific code generator.
 */
library class CodeGeneratorMarkerComment extends GeneratedCodeMarkerComment {
  CodeGeneratorMarkerComment() {
    codeGeneratorMarkerComment(this, _)
  }

  /** Gets the name of the code generator that left this marker comment. */
  string getGeneratorName() {
    codeGeneratorMarkerComment(this, result)
  }
}

/**
 * Holds if `c` is a comment left by code generator `tool`.
 */
private predicate codeGeneratorMarkerComment(SlashSlashComment c, string tool) {
  exists (string toolPattern |
    toolPattern = "js_of_ocaml|CoffeeScript|LiveScript|dart2js|ANTLR|PEG\\.js" and
    tool = c.getText().regexpCapture("\\s*Generated (from .*)?by (" + toolPattern + ")\\b.*", 1)
  )
}

/**
 * A generic generated code marker comment.
 */
private class GenericGeneratedCodeMarkerComment extends GeneratedCodeMarkerComment {
  GenericGeneratedCodeMarkerComment() {
    exists (string line | line = getLine(_) |
      exists (string entity, string was, string automatically |
        entity = "code|file|class|interface|art[ei]fact|module|script" and
        was = "was|is|has been" and
        automatically = "automatically |mechanically |auto[- ]?" and
        line.regexpMatch("(?i).*\\b(This|The following) (" + entity + ") (" +
                         was + ") (" + automatically + ")?gener(e?)ated\\b.*")
      )
    )
  }
}

/**
 * A comment warning against modifications, viewed as a marker comment indicating generated code.
 */
private class DontModifyMarkerComment extends GeneratedCodeMarkerComment {
  DontModifyMarkerComment() {
    exists (string line | line = getLine(_) |
      line.regexpMatch("(?i).*\\bGenerated by\\b.*\\bDo not edit\\b.*") or
      line.regexpMatch("(?i).*\\bAny modifications to this file will be lost\\b.*")
    )
  }
}

/** A script that looks like it was generated by dart2js. */
private class DartGeneratedTopLevel extends TopLevel {
  DartGeneratedTopLevel() {
    exists (VarAccess deferredInit | deferredInit.getTopLevel() = this |
      deferredInit.getName() = "$dart_deferred_initializers$" or
      deferredInit.getName() = "$dart_deferred_initializers"
    )
  }
}

/**
 * Holds if `tl` looks like it contains generated code.
 */
predicate isGenerated(TopLevel tl) {
  tl.isMinified() or
  isBundle(tl) or
  tl instanceof GWTGeneratedTopLevel or
  tl instanceof DartGeneratedTopLevel or
  exists (GeneratedCodeMarkerComment gcmc | tl = gcmc.getTopLevel())
}

/**
 * Holds if `file` look like it contains generated code.
 */
predicate isGeneratedCode(File file) {
  isGenerated(file.getATopLevel())
}
