open declarations

// Model the WebAuth Protocol

sig WAToken extends Token {}

// requester credentials
sig WAServiceToken extends WAToken { }
sig WAKrb5Token extends WAToken {}

// subject credentials

// The proxy token allow an application server to 
// retrieve sensitive information (e.g. a user's
// mails or LDAP data) on behalf of the user.
sig WAProxyToken extends WAToken{}

sig WALoginToken extends WAToken{}
sig WACredToken extends WAToken{}

// request token
sig WARequestToken extends Token {}

sig WARequest extends Token {
   msgId: lone Int
}

sig WAResponse extends Token {
   causedByMsgId: lone Int
}

sig WAGetTokenReq extends WARequest {
  reqCred:WAToken,
  subjCred:lone WAToken,
  reqToken:lone WARequestToken,
  tokens:set WAToken
}

sig WASessionKey extends Secret {}

sig WAGetTokenResp extends WAResponse {
  respTokens:set WAToken,
  sessionKey:WASessionKey
}

sig WARequestTokenReq extends WARequest {
  reqCred:WAServiceToken,
  proxyTokens:set WAProxyToken,
  loginTokens:WALoginToken,
  reqToken:WARequestToken,
  remoteUser:WebPrincipal
  // optional IP addresses go here
}

sig WAErrorToken extends WAToken {}
sig WAAppToken extends WAToken {} // opaque application token

sig WARequestTokenResp extends WAResponse {
  error:WAErrorToken,
  proxyToken:lone WAProxyToken, // for login request
  returnURL:URL,
  requesterSubject:Principal, // identity of requester
  subject:Principal, // identity in supplied credentials
  requestedToken:lone WAIdToken+WAProxyToken,
  loginCanceledToken:WAErrorToken,
  appState:WAAppToken
}

sig WAProxyData extends WAToken {} // may contain encrypted Krb data

// This command converts an existing Kerberos token 
// into a webkdc-proxy token, for improvied single sign-on.
sig WAProxyTokenReq extends WARequest {
  subjCred:WAToken,
  proxyData:WAProxyData
}

sig WAProxyTokenResp extends WAResponse {
  proxyToken:WAProxyToken,
  subject:WebPrincipal // identity from subject credential in the request
}

// This command extracts info from a proxy token
sig WAProxyTokenInfoReq extends WARequest {
  proxyToken:WAProxyToken
}

sig WAProxyTokenInfoResp extends WAResponse {
  subject:WebPrincipal, // identity from proxy token
  // proxy type
  creation:Time,
  expiration:Time
}

sig WANonce extends Token {}

// HMAC used in WebAuth. We may move them to a generic crypto file after we accumulate enough of them
sig WAHmac extends Token {} 

sig WAAttribute {name:Token, Value:Token}

sig WAEncryptedToken extends WAToken {
// 4-byte UTC time to tell the server which key was used to encrypt this token
  private keyHint:Token, 
  private nonce:WANonce,
  private hmac:WAHmac,
  // private attrs:set WAAttribute,
  private padding:Token
}
  
sig WAIdToken extends WAEncryptedToken{
  private username: WebPrincipal,
  // we don't need Kerberos subject authn data for now
  private creationTime: Time,
  private expirationTime: Time
}{
  // Token should normally expire within 5 minutes based on WebAuth spec. 
  // Simulate using 5 ticks
  expirationTime in creationTime.next.next.next.next.^next
}

pred WAContainsIdToken [resp:HTTPResponse, token:WAIdToken] {
  one (LocationHeader & resp.headers) and
  some locHdr: LocationHeader  |
    locHdr in resp.headers and
    locHdr.targetPath in WASAuthPath and
    token in locHdr.params.value
}

pred WAContainsIdToken [req:HTTPRequest, token:WAIdToken] {
  token in req.queryString.value 
}

pred WARemoteScriptingIsPossible {
  1 = 1  // true unless user disables script support
}

sig WASAuthPath extends Path {}
sig WAS extends HTTPServer {}
sig WAWebKDC extends HTTPServer {}

pred WAPossessTokenViaLogin[httpClient:HTTPClient, token:WAIdToken, usageEvent:Event]{
  some t1:HTTPTransaction|{
    happensBeforeOrdering[t1.req, usageEvent] and
    t1.req.path = LOGIN and 
    t1.req.to in WAWebKDC and
    t1.req.from in httpClient and
    t1.resp.statusCode in RedirectionStatus and
    WAContainsIdToken[t1.resp, token] and
    token.creationTime = t1.resp.post and
    token.username in httpClient.owner
  }
}

pred WAPossessTokenViaRemoteScripting [httpClient1:HTTPClient, token:WAIdToken, usageEvent:Event]{
  // Through remote scripting, some user2(say, Mallory) can pass information to user1(say, Alice)'s browser
  some t1:HTTPTransaction, httpClient2:HTTPClient|let user2=httpClient2.owner|
  {
    // Mallory possesses the token
    WAPossessTokenViaLogin[httpClient2, token, usageEvent] and
    // user1 (Alice) has a connection to user2(Mallory)'s web server
    happensBefore[t1.req, usageEvent] and 
    t1.req.from in httpClient1 and
    t1.req.to in (user2.servers & HTTPServer)
  } and {
    WARemoteScriptingIsPossible 
  }
}

fact WABeforeUsingTokenYouNeedToPossessIt{
  all httpClient:HTTPClient, req:HTTPRequest, token:WAIdToken | 
  {
    req.from in httpClient and 
    WAContainsIdToken [req, token]
  } implies
    WAPossessToken[httpClient, token, req]
}

pred WAPossessToken[httpClient:HTTPClient, token:WAIdToken, usageEvent:Event]{
  WAPossessTokenViaLogin [httpClient, token, usageEvent] or
  WAPossessTokenViaRemoteScripting [httpClient, token, usageEvent] 
}

// Constrain the web model in this module for better illustration.
// The general model does not enforce this.
fact WAHTTPFacts{
  all req:HTTPRequest | req.to in HTTPServer
  all user:WebPrincipal | user.servers in HTTPServer
  all t1:HTTPTransaction | some (t1.resp) implies (t1.req.from = t1.resp.to ) and (t1.req.to = t1.resp.from)
  Mallory.servers in (HTTPServer - (WAS+WAWebKDC))
}

pred WALoginCSRF [t1:HTTPTransaction]{
  some token:WAIdToken|{
    t1.req.from in Alice.httpClients and
    t1.req.path in WASAuthPath and
    t1.req.to in WAS and
    WAContainsIdToken [t1.req, token] and
    token.username in Mallory
  }
}

fun WAFindAttacks: HTTPTransaction{
  {
    t1:HTTPTransaction |
      WALoginCSRF[t1]
  }
}

// run WAFindAttacks for 8 but exactly 0 ACTIVEATTACKER, exactly 0 PASSIVEATTACKER
check WANoLoginCSRF {
  no WAFindAttacks
}
for 8 but exactly 0 ACTIVEATTACKER, exactly 0 PASSIVEATTACKER

/*
Executing "Check WANoLoginCSRF for 8 but exactly 0 ACTIVEATTACKER, exactly 0 PASSIVEATTACKER"
Run 1:
====
   Solver=minisat(jni) Bitwidth=4 MaxSeq=7 SkolemDepth=1 Symmetry=20
   Generating CNF...
   Generating the solution...
   Begin solveAll()
   194044 vars. 6761 primary vars. 386812 clauses. 601759ms.
   Solving...
   End solveAll()
   Counterexample found. Assertion is invalid. 10889ms.


*/


