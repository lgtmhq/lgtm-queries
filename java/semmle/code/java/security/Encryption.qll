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

import default

class SSLClass extends RefType {
  SSLClass() {
    exists(Class c | this.getASupertype*() = c |
	    (c.hasQualifiedName("javax.net.ssl", _)
	    or c.hasQualifiedName("javax.rmi.ssl", _))
    )
  }
}

/** A blacklist of algorithms that are known to be insecure. */
string algorithmBlacklist() {
  result = "DES" or
  result = "RC2" or
  result = "RC4" or 
  result = "RC5" or
  result = "ARCFOUR" // a variant of RC4
}

// These are only bad if they're being used for encryption.
string hashAlgorithmBlacklist() {
  result = "SHA1" or
  result = "MD5"
}

/** A regex for matching strings that look like they contain a blacklisted algorithm. */
string algorithmBlacklistRegex() {
  // In this case we know these are being used for encryption, so we want to match
  // weak hash algorithms too.
  exists(string s | s = algorithmBlacklist() or s = hashAlgorithmBlacklist() |
	  // Algorithms usually appear in names surrounded by characters that are not
	  // alphabetical characters in the same case. This handles the upper and lower
	  // case cases.
    result = "(^|.*[^A-Z])" + s + "([^A-Z].*|$)"
    // For lowercase, we want to be careful to avoid being confused by camelCase
	  // hence we require two preceding uppercase letters to be sure of a case switch,
	  // or a preceding non-alphabetic character
	  or result = "(^|.*[A-Z]{2}|.*[^a-zA-Z])" + s.toLowerCase() + "([^a-z].*|$)"
  )
}

/** A whitelist of algorithms that are known to be secure. */
string algorithmWhitelist() {
  result = "RSA" or
  result = "SHA256" or
  result = "CCM" or
  result = "GCM" or
  result = "AES" or
  result = "Blowfish" or
  result = "ECIES"
}

/** A regex for matching strings that look like they contain a whitelisted algorithm. */
string algorithmWhitelistRegex() {
  // The implementation of this is a duplicate of `algorithmBlacklistRegex`, as it isn't 
  // possible to have string -> string functions at the moment.
  
  // Algorithms usually appear in names surrounded by characters that are not
  // alphabetical characters in the same case. This handles the upper and lower
  // case cases.
  result = "(^|.*[^A-Z])" + algorithmWhitelist() + "([^A-Z].*|$)"
  // For lowercase, we want to be careful to avoid being confused by camelCase
  // hence we require two preceding uppercase letters to be sure of a case switch,
  // or a preceding non-alphabetic character
  or result = "(^|.*[A-Z]{2}|.*[^a-zA-Z])" + algorithmWhitelist().toLowerCase() + "([^a-z].*|$)"
}

/**
  * Any use of a cryptographic element that specifies an encryption
  * algorithm. For example, methods returning ciphers, decryption methods,
  * constructors of cipher classes, etc.
  */
abstract class CryptoAlgoSpec extends Top {
  CryptoAlgoSpec() { this instanceof Call }
  abstract Expr getAlgoSpec();
}

abstract class JavaxCryptoAlgoSpec extends CryptoAlgoSpec {}

class JavaxCryptoCipher extends JavaxCryptoAlgoSpec {
  JavaxCryptoCipher() {
    exists(Method m | m.getAReference() = this |
	    m.getDeclaringType().getQualifiedName() = "javax.crypto.Cipher" and
	    m.getName() = "getInstance"
    )
  }
  
  Expr getAlgoSpec() {
    result = ((MethodAccess)this).getArgument(0)
  }
}

class JavaxCryptoSecretKey extends JavaxCryptoAlgoSpec {
  JavaxCryptoSecretKey() {
    exists(Constructor c | c.getAReference() = this |
      c.getDeclaringType().getQualifiedName() = "javax.crypto.spec.SecretKeySpec"
    )
  }
  
  Expr getAlgoSpec() {
    exists(ConstructorCall c | c = this | 
      if c.getNumArgument() = 2
      then result = c.getArgument(1)
      else result = c.getArgument(3)
    )
  }
}

class JavaxCryptoKeyGenerator extends JavaxCryptoAlgoSpec {
  JavaxCryptoKeyGenerator() {
    exists(Method m | m.getAReference() = this |
      m.getDeclaringType().getQualifiedName() = "javax.crypto.KeyGenerator" and
      m.getName() = "getInstance"
    )
  }
  
  Expr getAlgoSpec() {
    result = ((MethodAccess)this).getArgument(0)
  }
}

class JavaxCryptoKeyAgreement extends JavaxCryptoAlgoSpec {
  JavaxCryptoKeyAgreement() {
    exists(Method m | m.getAReference() = this |
      m.getDeclaringType().getQualifiedName() = "javax.crypto.KeyAgreement" and
      m.getName() = "getInstance"
    )
  }
  
  Expr getAlgoSpec() {
    result = this.(MethodAccess).getArgument(0)
  }
}

class JavaxCryptoKeyFactory extends JavaxCryptoAlgoSpec {
  JavaxCryptoKeyFactory() {
    exists(Method m | m.getAReference() = this |
      m.getDeclaringType().getQualifiedName() = "javax.crypto.SecretKeyFactory" and
      m.getName() = "getInstance"
    )
  }
  
  Expr getAlgoSpec() {
    result = ((MethodAccess)this).getArgument(0)
  }
}

abstract class JavaSecurityAlgoSpec extends CryptoAlgoSpec {}

class JavaSecurityMessageDigest extends JavaSecurityAlgoSpec {
  JavaSecurityMessageDigest() {
    exists(Constructor c | c.getAReference() = this |
      c.getDeclaringType().getQualifiedName() = "java.security.MessageDigest"
    )
  }
  
  Expr getAlgoSpec() {
    result = ((ConstructorCall)this).getArgument(0)
  }
}

class JavaSecuritySignature extends JavaSecurityAlgoSpec {
  JavaSecuritySignature() {
    exists(Constructor c | c.getAReference() = this |
      c.getDeclaringType().getQualifiedName() = "java.security.Signature"
    )
  }
  
  Expr getAlgoSpec() {
    result = ((ConstructorCall)this).getArgument(0)
  }
}
