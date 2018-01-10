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
 * Provides classes for modelling cryptographic libraries.
 */


import javascript

/**
 * Names of cryptographic algorithms, separated into strong and weak variants.
 *
 * The names are normalized: upper-case, no spaces, dashes or underscores.
 *
 * The names are inspired by the names used in real world crypto libraries.
 *
 * The classification into strong and weak are based on Wikipedia, OWASP and google (2017).
 */
private module AlgorithmNames {
  predicate isStrongHashingAlgorithm(string name) {
    name = "DSA" or
    name = "ED25519" or
    name = "ES256" or name = "ECDSA256" or
    name = "ES384" or name = "ECDSA384" or
    name = "ES512" or name = "ECDSA512" or
    name = "SHA2" or
    name = "SHA224" or
    name = "SHA256" or
    name = "SHA384" or
    name = "SHA512" or
    name = "SHA3"
  }

  predicate isWeakHashingAlgorithm(string name) {
    name = "HAVEL128" or
    name = "MD2" or
    name = "MD4" or
    name = "MD5" or
    name = "PANAMA" or
    name = "RIPEMD" or
    name = "RIPEMD128" or
    name = "RIPEMD256" or
    name = "RIPEMD160" or
    name = "RIPEMD320" or
    name = "SHA0" or
    name = "SHA1"
  }

  predicate isStrongEncryptionAlgorithm(string name) {
    name = "AES" or
    name = "AES128" or
    name = "AES192" or
    name = "AES256" or
    name = "AES512" or
    name = "RSA" or
    name = "RABBIT" or
    name = "BLOWFISH"

  }

  predicate isWeakEncryptionAlgorithm(string name) {
    name = "DES" or
    name = "3DES" or name = "TRIPLEDES" or name = "TDEA" or name = "TRIPLEDEA" or
    name = "ARC2" or name = "RC2" or
    name = "ARC4" or name = "RC4" or name = "ARCFOUR" or
    name = "ARC5" or name = "RC5"
  }

  predicate isStrongPasswordHashingAlgorithm(string name) {
    name = "ARGON2" or
    name = "PBKDF2" or
    name = "BCRYPT" or
    name = "SCRYPT"
  }

  predicate isWeakPasswordHashingAlgorithm(string name) {
    none()
  }

  /**
   * Normalizes `name`: upper-case, no spaces, dashes or underscores.
   *
   * All names of this module are in this normalized form.
   */
  bindingset[name] string normalizeName(string name) {
    result = name.toUpperCase().regexpReplaceAll("[-_ ]", "")
  }
}
private import AlgorithmNames

/**
 * A cryptographic algorithm.
 */
private newtype TCryptographicAlgorithm =
MkHashingAlgorithm(string name, boolean isWeak) {
  (isStrongHashingAlgorithm(name) and isWeak = false) or
  (isWeakHashingAlgorithm(name) and isWeak = true)
} or
MkEncryptionAlgorithm(string name, boolean isWeak) {
  (isStrongEncryptionAlgorithm(name) and isWeak = false) or
  (isWeakEncryptionAlgorithm(name) and isWeak = true)
} or
MkPasswordHashingAlgorithm(string name, boolean isWeak) {
  (isStrongPasswordHashingAlgorithm(name) and isWeak = false) or
  (isWeakPasswordHashingAlgorithm(name) and isWeak = true)
}

/**
 * A cryptographic algorithm.
 */
abstract class CryptographicAlgorithm extends TCryptographicAlgorithm {

  /** Gets a textual representation of this element. */
  string toString() {
    result = getName()
  }

  /**
   * Gets the name of the algorithm.
   */
  abstract string getName();

  /**
   * Holds if this algorithm is weak.
   */
  abstract predicate isWeak();

}

/**
 * A hashing algorithm such as `MD5` or `SHA512`.
 */
class HashingAlgorithm extends MkHashingAlgorithm, CryptographicAlgorithm {

  string name;

  boolean isWeak;

  HashingAlgorithm() {
    this = MkHashingAlgorithm(name, isWeak)
  }

  override string getName() {
    result = name
  }

  override predicate isWeak() {
    isWeak = true
  }

}

/**
 * An encryption algorithm such as `DES` or `AES512`.
 */
class EncryptionAlgorithm extends MkEncryptionAlgorithm, CryptographicAlgorithm {

  string name;

  boolean isWeak;

  EncryptionAlgorithm() {
    this = MkEncryptionAlgorithm(name, isWeak)
  }

  override string getName() {
    result = name
  }

  override predicate isWeak() {
    isWeak = true
  }

}

/**
 * A password hashing algorithm such as `PBKDF2` or `SCRYPT`.
 */
class PasswordHashingAlgorithm extends MkPasswordHashingAlgorithm, CryptographicAlgorithm  {

  string name;

  boolean isWeak;

  PasswordHashingAlgorithm() {
    this = MkPasswordHashingAlgorithm(name, isWeak)
  }

  override string getName() {
    result = name
  }

  override predicate isWeak() {
    isWeak = true
  }
}

/**
 * An application of a cryptographic algorithm.
 */
abstract class CryptographicOperation extends Expr {

  /**
   * Gets the input the algorithm is used on, e.g. the plain text input to be encrypted.
   */
  abstract Expr getInput();

  /**
   * Gets the applied algorithm.
   */
  abstract CryptographicAlgorithm getAlgorithm();

}

/**
 * A model of the asmCrypto library.
 */
private module AsmCrypto {

  private class Apply extends CryptographicOperation {

    Expr input;

    CryptographicAlgorithm algorithm; // non-functional

    MethodCallExpr mce;

    Apply() {
      /*
      ```
      require("asmCrypto").SHA256.hex(input)
      ```
      matched as:
      ```
      require("asmCrypto").<algorithmName>._(<input>)
      ```
       */
      this = mce and
      exists(ModuleInstance mod, string algorithmName |
        mod.getPath() = "asmCrypto" and
        algorithm.getName() = normalizeName(algorithmName) and
        mce.getReceiver().(DataFlowNode).getALocalSource() = mod.getAPropertyRead(algorithmName) and
        input = mce.getAnArgument()
      )

    }

    override Expr getInput() {
      result = input
    }

    override CryptographicAlgorithm getAlgorithm() {
      result = algorithm
    }

  }

}

/**
 * A model of the browserid-crypto library.
 */
private module BrowserIdCrypto {

  private class Apply extends CryptographicOperation {

    Expr input;

    CryptographicAlgorithm algorithm; // non-functional

    MethodCallExpr mce;

    Apply() {
      /*
      ```
      var jwcrypto = require("browserid-crypto");
      jwcrypto.generateKeypair({algorithm: 'DSA'}, function(err, keypair) {
          jwcrypto.sign(input, keypair.secretKey);
        });
      ```
      matched as:
      ```
      var jwcrypto = require("browserid-crypto");
      jwcrypto.generateKeypair({algorithm: <algorithmName>}, function(err, keypair) {
          jwcrypto.sign(<input>, keypair.secretKey);
        });
      ```
       */
      this = mce and
      exists(ModuleInstance mod, DataFlowNode algorithmNameNode, MethodCallExpr keygen, Function callback, PropReadNode keyPrn |
        mod.getPath() = "browserid-crypto" and
        keygen = mod.getAMethodCall("generateKeypair") and
        keygen.hasOptionArgument(0,  "algorithm", algorithmNameNode) and
        algorithm.getName() = normalizeName(algorithmNameNode.getALocalSource().(ConstantString).getStringValue()) and
        keygen.getArgument(1).(DataFlowNode).getALocalSource() = callback and
        this = mod.getAMethodCall("sign") and
        mce.getArgument(0) = input and
        callback.getParameter(1).(SimpleParameter).getAnInitialUse() = keyPrn.getBase().(DataFlowNode).getALocalSource() and
        keyPrn.getPropertyName() = "secretKey" and
        mce.getArgument(1).(DataFlowNode).getALocalSource() = keyPrn
      )
    }

    override Expr getInput() {
      result = input
    }

    override CryptographicAlgorithm getAlgorithm() {
      result = algorithm
    }

  }

}

/**
 * A model of the Node.js builtin crypto library.
 */
private module NodeJSCrypto  {

  private class Apply extends CryptographicOperation {

    Expr input;

    CryptographicAlgorithm algorithm; // non-functional

    MethodCallExpr mce;

    Apply() {
      /*
      ```
      const crypto = require('crypto');
      const cipher = crypto.createCipher('aes192', 'a password');
      let encrypted = cipher.update('some clear text data', 'utf8', 'hex');
      ```
      matched as:
      ```
      const crypto = require('crypto');
      const cipher = crypto.createCipher(<algorithmName>, 'a password');
      let encrypted = cipher.update(<input>, 'utf8', 'hex');

      ```
      Also matches `createHash`, `createHmac`, `createSign` instead of `createCipher`.
      Also matches `write` instead of `update`.
       */
      this = mce and
      exists(ModuleInstance mod, MethodCallExpr createCall, string createSuffix |
        createSuffix = "Hash" or
        createSuffix = "Hmac" or
        createSuffix = "Sign" or
        createSuffix = "Cipher" |
        mod.getPath() = "crypto" and
        createCall = mod.getAMethodCall("create" + createSuffix) and
        algorithm.getName() = normalizeName(createCall.getArgument(0).(DataFlowNode).getALocalSource().(ConstantString).getStringValue()) and
        mce.getReceiver().(DataFlowNode).getALocalSource() = createCall and
        (mce.getMethodName() = "update" or mce.getMethodName() = "write") and
        mce.getArgument(0) = input
      )
    }

    override Expr getInput() {
      result = input
    }

    override CryptographicAlgorithm getAlgorithm() {
      result = algorithm
    }

  }

}


/**
 * A model of the crypto-js library.
 */
private module CryptoJS {

  /**
   *  Matches `CryptoJS.<algorithmName>` and `require("crypto-js/<algorithmName>")`
   */
  private Expr getAlgorithmExpr(CryptographicAlgorithm algorithm) {
    exists(string algorithmName |
      algorithm.getName() = normalizeName(algorithmName) |
      exists(ModuleInstance mod |
        mod.getPath() = "crypto-js" |
        result = mod.getAPropertyRead(algorithmName) or
        result = mod.getAPropertyRead("Hmac" + algorithmName) // they prefix Hmac
      ) or
      exists(ModuleInstance mod |
        mod.getPath() = "crypto-js/" + algorithmName  and
        result = mod
      )
    )
  }

  private MethodCallExpr getEncryptionApplication(Expr input, CryptographicAlgorithm algorithm) {
    /*
    ```
    var CryptoJS = require("crypto-js");
    CryptoJS.AES.encrypt('my message', 'secret key 123');
    ```
    Matched as:
    ```
    var CryptoJS = require("crypto-js");
    CryptoJS.<algorithmName>.encrypt(<input>, 'secret key 123');
    ```
    Also matches where `CryptoJS.<algorithmName>` has been replaced by `require("crypto-js/<algorithmName>")`
     */
    result.getReceiver().(DataFlowNode).getALocalSource() = getAlgorithmExpr(algorithm) and
    result.getMethodName() = "encrypt" and
    input = result.getArgument(0)
  }

  private CallExpr getDirectApplication(Expr input, CryptographicAlgorithm algorithm) {
    /*
    ```
    var CryptoJS = require("crypto-js");
    CryptoJS.SHA1("Message", "Key");
    ```
    Matched as:
    ```
    var CryptoJS = require("crypto-js");
    CryptoJS.<algorithmName>(<input>, "Key");
    ```
    An `Hmac`-prefix of <algorithmName> is ignored.
    Also matches where `CryptoJS.<algorithmName>` has been replaced by `require("crypto-js/<algorithmName>")`
     */
    result.getCallee().(DataFlowNode).getALocalSource() = getAlgorithmExpr(algorithm) and
    input = result.getArgument(0)
  }

   private class Apply extends CryptographicOperation {

    Expr input;

    CryptographicAlgorithm algorithm; // non-functional

    Apply() {
      this = getEncryptionApplication(input, algorithm) or
      this = getDirectApplication(input, algorithm)
    }

    override Expr getInput() {
      result = input
    }

    override CryptographicAlgorithm getAlgorithm() {
      result = algorithm
    }

  }

}

/**
 * A model of the TweetNaCl library.
 */
private module TweetNaCl {

  private class Apply extends CryptographicOperation {

    Expr input;

    CryptographicAlgorithm algorithm;

    MethodCallExpr mce;

    Apply() {
      /*
      ```
      require("nacl").sign('my message');
      ```
      Matched as:
      ```
      require("nacl").sign(<input>);
      ```
      Also matches the "hash" method name, and the "nacl-fast" module.
      */
      this = mce and
      exists(ModuleInstance mod, string name |
        (name = "hash" and algorithm.getName() = normalizeName("SHA512")) or
        (name = "sign" and algorithm.getName() = normalizeName("ed25519")) |
        (mod.getPath() = "nacl" or mod.getPath() = "nacl-fast") and
        mce = mod.getAMethodCall(name) and
        mce.getArgument(0) = input
      )
    }

    override Expr getInput() {
      result = input
    }

    override CryptographicAlgorithm getAlgorithm() {
      result = algorithm

    }

  }

}


/**
 * A model of the hash.js library.
 */
private module HashJs {

  /**
   *  Matches:
   * - `require("hash.js").<algorithmName>`()
   * - `require("hash.js/lib/hash/<algorithmName>")`()
   * - `require("hash.js/lib/hash/sha/<sha-algorithm-suffix>")`()
   */
  private CallExpr getAlgorithmExpr(CryptographicAlgorithm algorithm) {
    exists(string algorithmName |
      algorithm.getName() = normalizeName(algorithmName) |
      exists(ModuleInstance mod |
        mod.getPath() = "hash.js" |
        result = mod.getAMethodCall(algorithmName)
      ) or
      exists(ModuleInstance mod |
        mod.getPath() = "hash.js/lib/hash/" + algorithmName or
        exists(string size |
          mod.getPath() = "hash.js/lib/hash/sha/" + size and
          algorithmName = "SHA" + size) |
        result.getCallee().(DataFlowNode).getALocalSource() = mod
      )
    )
  }

   private class Apply extends CryptographicOperation {

    Expr input;

    CryptographicAlgorithm algorithm; // non-functional

    MethodCallExpr mce;

    Apply() {
      /*
      ```
      var hash = require("hash.js");
      hash.sha512().update('my message', 'secret key 123');
      ```
      Matched as:
      ```
      var hash = require("hash.js");
      hash.<algorithmName>().update('my message', 'secret key 123');
      ```
      Also matches where `hash.<algorithmName>()` has been replaced by a more specific require a la `require("hash.js/lib/hash/sha/512")`
       */
      this = mce and
      mce.getReceiver().(DataFlowNode).getALocalSource() = getAlgorithmExpr(algorithm) and
      mce.getMethodName() = "update" and
      input = mce.getArgument(0)
    }

    override Expr getInput() {
      result = input
    }

    override CryptographicAlgorithm getAlgorithm() {
      result = algorithm
    }

  }

}


/**
 * A model of the forge library.
 */
private module Forge  {

  private class Apply extends CryptographicOperation {

    Expr input;

    CryptographicAlgorithm algorithm; // non-functional

    MethodCallExpr mce;

    Apply() {
      this = mce and
      exists(ModuleInstance mod, MethodCallExpr cipher, string algorithmName |
        mce.getReceiver().(DataFlowNode).getALocalSource() = cipher and
        mce.getMethodName() = "update" and
        mce.getArgument(0) = input and
        algorithm.getName() = normalizeName(algorithmName) and
        (mod.getPath() = "forge" or mod.getPath() = "node-forge") |
        exists(string cipherName, string cipherPrefix, string cipherSuffix |
          // `require('forge').cipher.createCipher("3DES-CBC").update("secret");`
          cipher.getReceiver() = mod.getAPropertyRead("cipher") and
          cipher.getMethodName() = "createCipher" and
          cipher.getArgument(0).(DataFlowNode).getALocalSource().(ConstantString).getStringValue() = cipherName and
          cipherName = cipherPrefix + "-" + cipherSuffix and
          (
            cipherSuffix = "CBC" or
            cipherSuffix = "CFB" or
            cipherSuffix = "CTR" or
            cipherSuffix = "ECB" or
            cipherSuffix = "GCM" or
            cipherSuffix = "OFB"
          ) and
          algorithmName = cipherPrefix
        ) or
        (
          // `require("forge").rc2.createEncryptionCipher().update("secret");`
          cipher.getReceiver() = mod.getAPropertyRead(algorithmName) and
          cipher.getMethodName() = "createEncryptionCipher"
        ) or
        exists(PropReadNode algorithmObject |
          // require("forge").md.md5.create().update('The quick brown fox jumps over the lazy dog');
          algorithmObject.getBase().(DataFlowNode).getALocalSource() = mod.getAPropertyRead("md") and
          algorithmObject.getPropertyName() = algorithmName and
          cipher.getReceiver().(DataFlowNode).getALocalSource() = algorithmObject and
          cipher.getMethodName() = "create"
        )
      )
    }

    override Expr getInput() {
      result = input
    }

    override CryptographicAlgorithm getAlgorithm() {
      result = algorithm
    }

  }

}

/**
 * A model of the md5 library.
 */
private module Md5  {

  private class Apply extends CryptographicOperation {

    Expr input;

    CryptographicAlgorithm algorithm;

    CallExpr call;

    Apply() {
      // `require("md5")("message");`
      this = call and
      exists(ModuleInstance mod |
        mod.getPath() = "md5" and
        algorithm.getName() = normalizeName("MD5") and
        call.getCallee().(DataFlowNode).getALocalSource() = mod and
        call.getArgument(0) = input
      )
    }

    override Expr getInput() {
      result = input
    }

    override CryptographicAlgorithm getAlgorithm() {
      result = algorithm
    }

  }

}

/**
 * A model of the bcrypt, bcryptjs, bcrypt-nodejs libraries.
 */
private module Bcrypt  {

  private class Apply extends CryptographicOperation {

    Expr input;

    CryptographicAlgorithm algorithm;

    MethodCallExpr mce;

    Apply() {
      // `require("bcrypt").hash(password);` with minor naming variations
      this = mce and
      exists(ModuleInstance mod, string moduleName, string methodName |
        algorithm.getName() = normalizeName("BCRYPT") and
        (
          moduleName = "bcrypt" or
          moduleName = "bcryptjs" or
          moduleName = "bcrypt-nodejs"
        ) and (
          methodName = "hash" or
          methodName = "hashSync"
        ) and
        mod.getPath() = moduleName and
        mce = mod.getAMethodCall(methodName) and
        mce.getArgument(0) = input
      )
    }

    override Expr getInput() {
      result = input
    }

    override CryptographicAlgorithm getAlgorithm() {
      result = algorithm
    }

  }

}

/**
 * A model of the hasha library.
 */
private module Hasha  {

  private class Apply extends CryptographicOperation {

    Expr input;

    CryptographicAlgorithm algorithm;

    CallExpr call;

    Apply() {
      // `require('hasha')('unicorn', { algorithm: "md5" });`
      this = call and
      exists(ModuleInstance mod, string algorithmName, DataFlowNode algorithmNameNode |
        mod.getPath() = "hasha" and
        call.getCallee().(DataFlowNode).getALocalSource() = mod and
        call.getArgument(0) = input and
        algorithm.getName() = normalizeName(algorithmName) and
        call.hasOptionArgument(1, "algorithm", algorithmNameNode) and
        algorithmName = algorithmNameNode.getALocalSource().(ConstantString).getStringValue()
      )
    }

    override Expr getInput() {
      result = input
    }

    override CryptographicAlgorithm getAlgorithm() {
      result = algorithm
    }

  }

}
