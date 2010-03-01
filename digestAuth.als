open declarations

// model digest auth 
/***
Possible attacks
1. MITM, once the user logs in, active attacker can intercept and modify the server response to 302 redirect to url of the attacker's choice. The browser will fill in digest auth token w/o input from the user. The server serves the protected doc of the attacker's choice. The attacker fakes another 302 to redirect the browser back to the original url, or alternatively caches the original content and sends it to the browser at the end. The user may not detect any abnormaly except possibly a slower response from the server. 
2. Most of the req headers are not protected by digest, and can be modified at will by the attacker.
3. Request / response splitting. however, fixing this vulnerability is relatively easy at the implementation level. One needs to filter away CR/LF characters, whereas the attacks #1 and #2 reveal protocol weaknesses.
***/

// Message strctures as defined in RFC2617

// realm+user+pass+nonce are hashed in all modes of digest auth
// requested URI possibly combined with other info determines the realm of identities accepted for digest auth

sig DigestRealm extends Token {}
sig DigestQOP extends Token {}
sig DigestNonce extends Token {}

// Server's challenge to user agent
sig DigestAuthChallenge extends Token{
  realm:DigestRealm,
  nonce:DigestNonce,
  qop:DigestQOP 
  // The quality of protections accepted by the server
  // Assume the higest quality of protection here, as trivial attacks exist at lower level.
}{}

// Intermediate hash value computed by both server and user agent
sig DigestHashA1 extends Token{
  // technically the username:realm:password combo may be hashed twice in A1. 
  // This is irrelevant here if we assume the hashing algorithm is secure.
  private username:WebPrincipal,
  private realm:DigestRealm,
  private password:UserPassword,
  private nonce:DigestNonce,
  private cnonce:DigestNonce
}{}

sig DigestRequestEntityBodyHash extends Token {
  private body:set Token // HTTP request body
}{}

// Hash of A2 computed by user agent
sig DigestHashA2U extends Token{
  private method:Method,
  private requestedURI:Path,
  private requestBodyHash: DigestRequestEntityBodyHash
}{}

// Hash of A2 computed by server. The Method field is skipped.
sig DigestHashA2S extends Token{
  private requestedURI:Path,
  private requestBodyHash: DigestRequestEntityBodyHash
}{}

// Hash of digest response computed by user agent
sig DigestHashResponseU extends Token{
  private hashA1:DigestHashA1,
  private nonce:DigestNonce,
  private nonceCount:Int,
  private cnonce:DigestNonce,
  private qop:DigestQOP, 
  private hashA2U:DigestHashA2U
}{}

// Hash of digest response computed by server
sig DigestHashResponseS extends Token{
  private hashA1:DigestHashA1,
  private nonce:DigestNonce,
  private nonceCount:Int,
  private cnonce:DigestNonce,
  private qop:DigestQOP, 
  private hashA2S:DigestHashA2S
}{}

sig DigestAuthResponseU extends Token{
  username:WebPrincipal,
  realm:DigestRealm,
  nonce:DigestNonce,
  requestedURI:Path, 
  digestHashResponseU:DigestHashResponseU,
  qop:DigestQOP, 
  // quality of protection chosen by the user agent
  // Assume the higest quality of protection here, as trivial attacks exist at lower level.
  cnonce:DigestNonce,
  nonceCount:Int
}{}

sig DigestAuthInfo{
  nextNonce:DigestNonce,
  qop:DigestQOP, 
  // qop should be the same as in DigestAuthResponseU. 
  // Here we assume the highest level of protection is chosen.
  digestHashResponseS:DigestHashResponseS,
  cnonce:DigestNonce,
  nonceCount:Int
}{}

sig DigestWWWAuthnHeader extends WWWAuthnHeader   
{
  digestChallenge:DigestAuthChallenge // challenge of digest auth
}

sig DigestAuthzHeader extends HTTPRequestHeader {
  digestResponseU:DigestAuthResponseU  // User Agent's response to digest auth
}{}

sig DigestAuthnInfoHeader extends HTTPResponseHeader {
  digestAuthInfo:DigestAuthInfo
}{}

// return the transaction that contains the previous Digest challenge
fun DigestPrevChallenge[t1:HTTPTransaction] : HTTPTransaction {
  { t0:HTTPTransaction | // t0 contains a digest challenge for the given path
    happensBeforeOrdering[t0.resp, t1.req] and 
    t1.req.path = t0.req.path and 
    ( some (t0.resp.headers & DigestWWWAuthnHeader).digestChallenge) and
    no t2:HTTPTransaction |{ // the challenge(nonce) in t0 has not been responded to the server
      happensBeforeOrdering[t2.req, t1.req] and 
      happensBeforeOrdering[t0.resp, t2.req] and 
      let t2DigestResponseU = (t2.req.headers & DigestAuthzHeader).digestResponseU |
      let t1Header=(DigestAuthzHeader& t1.req.headers) | {
        (t1Header.digestResponseU).requestedURI = t2DigestResponseU.requestedURI     and  
        t2DigestResponseU.requestedURI = t2DigestResponseU.digestHashResponseU.hashA2U.requestedURI and 
        t2DigestResponseU.username = t2DigestResponseU.digestHashResponseU.hashA1.password.id and 
        t2DigestResponseU.nonce = ( t0.resp.headers & DigestWWWAuthnHeader).digestChallenge.nonce and
        t2DigestResponseU.realm = ( t0.resp.headers & DigestWWWAuthnHeader).digestChallenge.realm and
        t2.req.body = t2DigestResponseU.digestHashResponseU.hashA2U.requestBodyHash.body and 
        some t2.resp // i.e. t1.req has been received by the server
      }
    }
  }
}

pred containsValidDigestAuthResponseU [t1:HTTPTransaction] {
  some (t1.req.headers & DigestAuthzHeader).digestResponseU and 
  let dRU1 = (t1.req.headers & DigestAuthzHeader).digestResponseU |{
  // chk uri, pwd, nonce, realm, body hash, etc
    dRU1.requestedURI = dRU1.digestHashResponseU.hashA2U.requestedURI and 
    dRU1.username = dRU1.digestHashResponseU.hashA1.password.id and 
    dRU1.nonce = ( (DigestPrevChallenge[t1]).resp.headers & DigestWWWAuthnHeader).digestChallenge.nonce and
    dRU1.realm = ( (DigestPrevChallenge[t1]).resp.headers & DigestWWWAuthnHeader).digestChallenge.realm and
    t1.req.body = dRU1.digestHashResponseU.hashA2U.requestBodyHash.body 
  }
}

pred hasDigestKnowledgeViaHTTP[token: DigestAuthResponseU,  usageEvent: Event]{
  some t1 : HTTPTransaction | {
    happensBeforeOrdering[t1.req,usageEvent] and 
    t1.req.host.schema = HTTP and 
    containsValidDigestAuthResponseU[t1] and 
    token = (t1.req.headers & DigestAuthzHeader).digestResponseU
  }
}

pred hasDigestKnowledgeViaDirectHTTP[token: DigestAuthResponseU,  ne:NetworkEndpoint,usageEvent:Event]{
  some t1: HTTPTransaction | {
    happensBeforeOrdering[t1.req, usageEvent] and
    containsValidDigestAuthResponseU[t1] and 
    token = (t1.req.headers & DigestAuthzHeader).digestResponseU and
    ((t1.req.from = ne) or (t1.req.to = ne) or ne in ACTIVEATTACKER.servers)
    // fact: active attacker can read/write http traffic, but cannot recover the private fields in hash
  } 
}


fact BeforeUsingDigestTokenYouNeedToKnowAboutIt{
  /*
  all t1:HTTPTransaction |
    containsValidDigestAuthResponseU[t1] => 
  */
  all req:HTTPRequest | 
    all token:(req.headers & DigestAuthzHeader).digestResponseU  |
        hasDigestKnowledge[token , req.from, req]
}


pred hasDigestKnowledge[token: DigestAuthResponseU, ne:NetworkEndpoint,usageEvent:Event]{
  hasDigestKnowledgeViaHTTP[token,usageEvent] or hasDigestKnowledgeViaDirectHTTP[token,ne,usageEvent] or
  ( 
    // We need at least one person who can login via Digest Auth.
    token.digestHashResponseU.hashA1.password.id=Alice and 
    token.username = Alice and isAuthorizedAccess[Alice, ne]
  )
}

pred isLoggedInViaDigest [t: HTTPTransaction ] {
   t.req.path in SENSITIVE  and  containsValidDigestAuthResponseU [t]
}
 
fact DigestSomeUserCanAccessProtectedPath {
  some DigestAuthResponseU 
  some t1:HTTPTransaction| {
    t1.req.path=SENSITIVE and  
    containsValidDigestAuthResponseU[t1]    
    and (t1.req.headers & DigestAuthzHeader).digestResponseU.username = Alice
    and isAuthorizedAccess[Alice, t1.req.from]
  }
  // also remove irrelevant types
  /*
  no DELETE
  no OPTIONS 
  */
  // no ScriptContext
}
  
pred digestChosenURIAccessByAttackers [t1:HTTPTransaction]{ 
    (containsValidDigestAuthResponseU[t1]) and 
    all req1:(t1.req) | { 
      (req1.from in ((PASSIVEATTACKER+ACTIVEATTACKER+WEBATTACKER).servers)) and
      (req1.path=PATH_TO_COMPROMISE) and  
      (not isAuthorizedAccess[Alice, req1.from]) and 
      ((req1.headers & DigestAuthzHeader).digestResponseU.username = Alice) 

    }

}

// declare this as a fact and then try to construct a model consistent with all the facts 
fact digestAttacks { 
  some t1:HTTPTransaction | 
    digestChosenURIAccessByAttackers[t1]
}

fun findDigestAttacks: HTTPTransaction{ 
  {
    t1:HTTPTransaction | 
      digestChosenURIAccessByAttackers[t1]
  }
}

// run digestAttacks {} for 10 
run findDigestAttacks for 10 but
2 Origin,  5 HTTPTransaction, 1 String1, 
2 WebPrincipal,  1 OriginHeader, 1 Certificate,
3 UserToken, 3 DNS,
5 HTTPRequest, 5 HTTPResponse
, 1 Alice
, 0 PassPetPassword 
, 0 RequestAPI
, 0 LOGIN
, 0 LOGOUT
, 1 UserPassword
, 1 PATH_TO_COMPROMISE 
 
  
/*
Executing "Run findDigestAttacks for 10 but 2 Origin, 5 HTTPTransaction, 1 String1, 2 User, 1 OriginHeader, 1 Certificate, 3 UserToken, 3 DNS, 5 HTTPRequest, 5 HTTPResponse"
   Solver=minisat(jni) Bitwidth=4 MaxSeq=7 SkolemDepth=1 Symmetry=20
   142038 vars. 7714 primary vars. 347555 clauses. 277158ms.
   Instance found. Predicate is consistent. 3416ms.
*/

/* 
  run digestAttacks {} for 10 
  Solver=sat4j Bitwidth=4 MaxSeq=7 SkolemDepth=1 Symmetry=20
   Generating CNF...
   Generating the solution...
   Begin solveAll()
   236964 vars. 10601 primary vars. 589662 clauses. 1290894ms.
   Solving...
   End solveAll()
   . found. Predicate is consistent. 44445ms.
*/
