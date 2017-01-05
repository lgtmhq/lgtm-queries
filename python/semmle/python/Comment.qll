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

import python

/** A source code comment */
class Comment extends @py_comment {

    /** the text of the comment */
    string getText() {
    		py_comments(this, result, _)
    }

    Location getLocation() {
        py_comments(this, _, result)

    }

    string toString() {
        result = "Comment " + this.getText()
    }
    
    /** Gets this immediately following comment. 
     * Blanks line are allowed between this comment and the following comment,
     * but code or other comments are not.
     */
    Comment getFollowing() {
        exists(File f, int n |
            this.file_line(f, n) |
            result.file_line(f, n+1) 
            or
            result.file_line(f, n+2) and f.emptyLine(n+1) 
            or
            result.file_line(f, n+3) and f.emptyLine(n+2) and f.emptyLine(n+1)
        )
    }
    
    private predicate file_line(File f, int n) {
        this.getLocation().getFile() = f and
        this.getLocation().getStartLine() = n
    }
    
}

private predicate comment_block_part(Comment start, Comment end) {
    not exists(Comment prev | prev.getFollowing() = start) and
    end = start.getFollowing()
    or
    exists(Comment mid |
        comment_block_part(start, mid) and
        end = mid.getFollowing()
    )
}

/** A block of consecutive comments */
class CommentBlock extends @py_comment {
  
    CommentBlock() {
        comment_block_part(this, _)
    }
    
    private Comment last() {
        comment_block_part(this, result) and
        not exists(result.getFollowing())
    }
    
    string toString() {
        result = "Comment block" 
    }
    
    /** The length of this comment block (in comments) */
    int length() {
        result = count(Comment c | this.contains(c))
    }
    
    predicate hasLocationInfo(string filepath, int bl, int bc, int el, int ec) {
        ((Comment)this).getLocation().hasLocationInfo(filepath, bl, bc, _, _)
        and
        exists(Comment end |
            end = this.last() |
            end.getLocation().hasLocationInfo(_, _, _, el, ec)
        )
    }
    
    predicate contains(Comment c) {
        comment_block_part(this, c)
        or
        this = c
    }

}

