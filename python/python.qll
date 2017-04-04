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

import semmle.python.Files
import semmle.python.Operations
import semmle.python.Variables
import semmle.python.AstGenerated
import semmle.python.AstExtended
import semmle.python.AST
import semmle.python.Function
import semmle.python.Module
import semmle.python.Class
import semmle.python.Import
import semmle.python.Stmts
import semmle.python.Exprs
import semmle.python.Keywords
import semmle.python.Comprehensions
import semmle.python.Lists
import semmle.python.Flow
import semmle.python.Metrics
import semmle.python.Constants
import semmle.python.Scope
import semmle.python.Comment
import semmle.python.GuardedControlFlow
import semmle.python.types.ImportTime
import semmle.python.types.Object
import semmle.python.pointsto.Final
import semmle.python.types.Object
import semmle.python.types.ClassObject
import semmle.python.types.FunctionObject
import semmle.python.types.ModuleObject
import semmle.python.types.Version
import semmle.python.protocols
import semmle.python.SSA
import semmle.python.Assigns
import semmle.python.SelfAttribute
import semmle.python.types.Properties
import semmle.python.xml.XML

import site