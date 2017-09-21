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
 * Provides classes for working with NoSQL libraries.
 */

import javascript

module NoSQL {
  /** An expression that is interpreted as a NoSQL query. */
  abstract class Query extends DataFlowNode {
  }
}

/**
 * Provides classes modeling the MongoDB library.
 */
private module MongoDB {
  /**
   * Gets an expression that may refer to an import of MongoDB.
   */
  private DataFlowNode getAMongoDBInstance() {
    result.getALocalSource().(ModuleInstance).getPath() = "mongodb"
  }

  /**
   * Gets an expression that may refer to `mongodb.MongoClient`.
   */
  private DataFlowNode getAMongoClient() {
    result.getALocalSource().(PropAccess).accesses(getAMongoDBInstance(), "MongoClient")
  }

  /**
   * Gets an expression that may refer to a MongoDB database connection.
   */
  private DataFlowNode getAMongoDb() {
    exists (MethodCallExpr connect, Function cb |
      connect.calls(getAMongoClient(), "connect") and
      cb = connect.getArgument(1).(DataFlowNode).getALocalSource() and
      result.getALocalSource().(VarAccess).getVariable() = cb.getParameter(1).(SimpleParameter).getVariable()
    )
  }

  /**
   * An expression that may hold a MongoDB collection.
   */
  abstract class Collection extends DataFlowNode {
  }

  /**
   * A collection resulting from calling `Db.collection(...)`.
   */
  private class CollectionFromDb extends Collection {
    CollectionFromDb() {
      exists (MethodCallExpr collection | collection.calls(getAMongoDb(), "collection") |
        this.getALocalSource() = collection
        or
        exists (Function cb |
          cb = collection.getArgument(1).(DataFlowNode).getALocalSource() and
          this.getALocalSource().(VarAccess).getVariable() = cb.getParameter(1).(SimpleParameter).getVariable()
        )
      )
    }
  }

  /**
   * An expression that is interpreted as a MongoDB query.
   */
  class Query extends NoSQL::Query {
    Query() {
      exists (MethodCallExpr mce, string m | mce.calls(any(Collection c), m) |
        m = "count" and this = mce.getArgument(0) or
        m = "distinct" and this = mce.getArgument(1) or
        m = "find" and this = mce.getArgument(0)
      )
    }
  }
}

/**
 * Provides classes modeling the Mongoose library.
 */
module Mongoose {
  /**
   * Gets an expression that may refer to an import of Mongoose.
   */
  private DataFlowNode getAMongooseInstance() {
    result.getALocalSource().(ModuleInstance).getPath() = "mongoose"
  }

  /**
   * A Mongoose collection object.
   */
  class Model extends MongoDB::Collection {
    Model() {
      this.getALocalSource().(MethodCallExpr).calls(getAMongooseInstance(), "model")
    }
  }
}
