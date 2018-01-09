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

import cpp

class ExternalData extends @externalDataElement {

  string getDataPath() { externalData(this, result, _, _) }

  string getQueryPath() { result = getDataPath().regexpReplaceAll("\\.[^.]*$", ".ql") }

  int getNumFields() { result = 1 + max(int i | externalData(this, _, i, _) | i) }

  string getField(int index) { externalData(this, _, index, result) }

  int getFieldAsInt(int index) { result = getField(index).toInt() }

  float getFieldAsFloat(int index) { result = getField(index).toFloat() }

  date getFieldAsDate(int index) { result = getField(index).toDate() }

  string toString() { 
    result = getQueryPath() + ": " + buildTupleString(0)
  }
  
  private string buildTupleString(int start) {
    (start = getNumFields() - 1 and result = getField(start))
    or
    (start < getNumFields() - 1 and result = getField(start) + "," + buildTupleString(start+1))
  }

}

/**
 * External data with a location, and a message, as produced by tools that used to produce QLDs.
 */
class DefectExternalData extends ExternalData {
  DefectExternalData() { 
    this.getField(0).regexpMatch("\\w+://.*:[0-9]+:[0-9]+:[0-9]+:[0-9]+$") and
    this.getNumFields() = 2
  }
  
  string getURL() { result = getField(0) }

  string getMessage() { result = getField(1) }
}

