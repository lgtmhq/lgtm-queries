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
 * A library for working with J2EE bean types.
 */

import Type

/** An entity bean. */
class EntityBean extends Class {
  EntityBean() {
    exists(Interface i | i.hasQualifiedName("javax.ejb","EntityBean") |
      this.hasSupertype+(i)
    )
  }
}

/** An enterprise bean. */
class EnterpriseBean extends RefType {
  EnterpriseBean() {
    exists(Interface i | i.hasQualifiedName("javax.ejb","EnterpriseBean")  |
      this.hasSupertype+(i)
    )
  }
}

/** A local EJB home interface. */
class LocalEJBHomeInterface extends Interface {
  LocalEJBHomeInterface() {
    exists(Interface i | i.hasQualifiedName("javax.ejb","EJBLocalHome")  |
      this.hasSupertype+(i)
    )
  }
}

/** A remote EJB home interface. */
class RemoteEJBHomeInterface extends Interface {
  RemoteEJBHomeInterface() {
    exists(Interface i | i.hasQualifiedName("javax.ejb","EJBHome")  |
      this.hasSupertype+(i)
    )
  }
}

/** A local EJB interface. */
class LocalEJBInterface extends Interface {
  LocalEJBInterface() {
    exists(Interface i | i.hasQualifiedName("javax.ejb","EJBLocalObject")  |
      this.hasSupertype+(i)
    )
  }
}

/** A remote EJB interface. */
class RemoteEJBInterface extends Interface {
  RemoteEJBInterface() {
    exists(Interface i | i.hasQualifiedName("javax.ejb","EJBObject")  |
      this.hasSupertype+(i)
    )
  }
}

/** A message bean. */
class MessageBean extends Class {
  MessageBean() {
    exists(Interface i | i.hasQualifiedName("javax.ejb","MessageDrivenBean")  |
      this.hasSupertype+(i)
    )
  }
}

/** A session bean. */
class SessionBean extends Class {
  SessionBean() {
    exists(Interface i | i.hasQualifiedName("javax.ejb","SessionBean")  |
      this.hasSupertype+(i)
    )
  }
}