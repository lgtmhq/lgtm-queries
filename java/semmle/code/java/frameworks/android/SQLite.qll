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

import java

class TypeSQLiteDatabase extends Class {
  TypeSQLiteDatabase() {
    hasQualifiedName("android.database.sqlite", "SQLiteDatabase")
  }
}

abstract class SQLiteRunner extends Method {
  abstract int sqlIndex();
}

class ExecSqlMethod extends SQLiteRunner {
  ExecSqlMethod() {
    this.getDeclaringType() instanceof TypeSQLiteDatabase and
    this.getName() = "execSql"
  }
  
  int sqlIndex() { result = 0 }
}

class QueryMethod extends SQLiteRunner {
  QueryMethod() {
    this.getDeclaringType() instanceof TypeSQLiteDatabase and
    this.getName().matches("rawQuery%")
  }
  
  int sqlIndex() {
    this.getName() = "query" and 
    (
      if this.getParameter(0).getType() instanceof TypeString 
      then result = 2 
      else result = 3
    ) or
    this.getName() = "queryWithFactory" and result = 4
  }
}

class RawQueryMethod extends SQLiteRunner {
  RawQueryMethod() {
    this.getDeclaringType() instanceof TypeSQLiteDatabase and
    this.getName().matches("rawQuery%")
  }
  
  int sqlIndex() {
    this.getName() = "rawQuery" and result = 0 or
    this.getName() = "rawQueryWithFactory" and result = 1
  }
}
