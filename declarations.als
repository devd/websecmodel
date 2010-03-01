open util/ordering[Time]

sig DNS{
	parent : DNS + DNSRoot,
	resolvesTo : set NetworkEndpoint
}{
// A DNS Label resolvesTo something
	some resolvesTo
}

one sig DNSRoot {}

fact dnsIsAcyclic {
	 all x: DNS | x !in x.^parent
//	 all x:dns-dnsRoot | some x.parent
}

// s is  a subdomain of d
pred isSubdomainOf[s: DNS, d: DNS]{
  // e.g. .stanford.edu is a subdomain of .edu
  d in s.*parent
}


abstract sig Principal {
// without the -HTTPClient the HTTPS check fails
	servers : set NetworkEndpoint,
	dnslabels : set DNS,
}

fun getPrincipalFromDNS[dns : DNS]:Principal{
	dnslabels.dns
}

fun getPrincipalFromOrigin[o: Origin]:Principal{
	getPrincipalFromDNS[o.dnslabel]
}

fact DNSIsDisjointAmongstPrincipals {
	all disj p1,p2 : Principal | (no (p1.dnslabels & p2.dnslabels)) and ( no (p1.servers & p2.servers)) 
//The servers disjointness is a problem for virtual hosts. We will replace it with disjoint amongst attackers and trusted people or something like that
}

// turn this on for intermediate checks
// run show {} for 6

sig Time {}

abstract sig Token {}

abstract sig Secret extends Token {
	madeBy : Principal,
	expiration : lone Time,

}

// second.pre >= first.post
pred happensBeforeOrdering[first:Event,second:Event]{
	second.pre in first.post.*next
}

// shorter name
pred happensBefore[first:Event,second:Event]{
	second.pre in first.post.*next
}

fact Traces{
	all t:Time- last | one e:Event | e.pre=t and e.post=t.next
	all e:Event | e.post=e.pre.next
}


sig NetworkEndpoint{}

abstract sig Event {pre,post : Time} { }

abstract sig NetworkEvent extends Event {
    from: NetworkEndpoint,
    to: NetworkEndpoint
}

// we don't make HTTPServer abstract, it will be defined by the owner

abstract sig HTTPConformist extends NetworkEndpoint{}
sig HTTPServer extends HTTPConformist{}
abstract sig HTTPClient extends HTTPConformist{ 
  owner:WebPrincipal // owner of the HTTPClient process
}
sig Browser extends HTTPClient {
	trustedCA : set certificateAuthority
}
sig InternetExplorer extends Browser{}
sig InternetExplorer7 extends InternetExplorer{}
sig InternetExplorer8 extends InternetExplorer{}
sig Firefox extends Browser{}
sig Firefox3 extends Firefox {}
sig Safari extends Browser{}

abstract sig Method {}
one sig GET extends Method {}
one sig PUT  extends Method {}
one sig POST extends Method {}
one sig DELETE extends Method {}
one sig OPTIONS extends Method {}

fun safeMethods[]:set Method {
	GET+OPTIONS
}

abstract sig HTTPHeader {}
abstract sig HTTPResponseHeader extends HTTPHeader{} 
abstract sig HTTPRequestHeader extends HTTPHeader{}
abstract sig Status  {}
abstract sig RedirectionStatus extends Status {}

fact noOrphanedHeaders {
  all h:HTTPRequestHeader|some req:HTTPRequest|h in req.headers
  all h:HTTPResponseHeader|some resp:HTTPResponse|h in resp.headers
}

//////////////////
//////////////////
//////////////////

abstract sig HTTPEvent extends NetworkEvent { host : Origin }

sig URL {path:Path, host:Origin}

sig HTTPRequest extends HTTPEvent { 
  // host + path == url
  method: Method,
  path : Path,
  queryString : set attributeNameValuePair,  // URL query string parameters
  headers : set HTTPRequestHeader,
  body :  set Token
}

sig HTTPResponse extends HTTPEvent {
		statusCode : Status ,
		headers : set HTTPResponseHeader
}


// Browsers run a scriptContext
sig ScriptContext { 
	owner : Origin,
	location : Browser,
	transactions: set HTTPTransaction
}{
// Browsers are honest, they set the from correctly
	transactions.req.from = location
}


lone sig c301,c302,c303,c304,c305,c306,c307 extends RedirectionStatus {}
lone sig c200,c401 extends Status{}
sig location extends HTTPResponseHeader {targetOrigin : Origin, targetPath : Path}
// The name location above easily conflicts with other attributes and variables with the same name. 
// We should follow the convention of starting type names with a capital letter.
// Address this in later clean-up.

sig attributeNameValuePair { name: Token, value: Token}

sig LocationHeader extends HTTPResponseHeader {
  targetOrigin : Origin,
  targetPath : Path,
  params : set attributeNameValuePair  // URL request parameters
}

abstract sig RequestAPI // extends Event 
{} 

sig HTTPTransaction {
	req : HTTPRequest,
	resp : lone HTTPResponse,
	cert : lone Certificate,
	cause : lone HTTPTransaction + RequestAPI
}{
	some resp implies {
		//response can come from anyone but HTTP needs to say it is from correct person and hosts are the same, so schema is same
		resp.host = req.host
		happensBeforeOrdering[req,resp]
	}

	req.host.schema = HTTPS implies some cert and some resp 
	some cert implies req.host.schema = HTTPS

}

fact CauseHappensBeforeConsequence  {
	all t1: HTTPTransaction | some (t1.cause) implies {
       (some t0:HTTPTransaction | (t0 in t1.cause and happensBeforeOrdering[t0.resp, t1.req]))  
       or (some r0:RequestAPI | (r0 in t1.cause ))
       // or (some r0:RequestAPI | (r0 in t1.cause and happensBeforeOrdering[r0, t1.req]))
    }
}

fun getTrans[e:HTTPEvent]:HTTPTransaction{
	(req+resp).e
}

fun getScriptContext[t:HTTPTransaction]:ScriptContext {
		transactions.t
}




fun getContextOf[request:HTTPRequest]:Origin {
	(transactions.(req.request)).owner
}

pred isCrossOriginRequest[request:HTTPRequest]{
		getContextOf[request].schema != request.host.schema or
		getContextOf[request].dnslabel != request.host.dnslabel
}

// moved CORS to a separate file cors.alf for modularization

/************************************
* CSRF
*
************************************/


// RFC talks about having Origin Chain and not a single Origin
// We handle Origin chain by having multiple Origin Headers 
sig OriginHeader extends HTTPRequestHeader {theorigin: Origin}


fun getFinalResponse[request:HTTPRequest]:HTTPResponse{
        {response : HTTPResponse | not ( response.statusCode in RedirectionStatus) and response in ((req.request).*(~cause)).resp}
}

pred isFinalResponseOf[request:HTTPRequest, response : HTTPResponse] {
       not ( response.statusCode in RedirectionStatus)
       response in ((req.request).*(~cause)).resp
}




//enum Port{P80,P8080}
enum Schema{HTTP,HTTPS}
sig Path{}
sig INDEX,HOME,SENSITIVE, PUBLIC, LOGIN,LOGOUT,REDIRECT extends Path{}
sig PATH_TO_COMPROMISE extends SENSITIVE {}

// sig User extends WebPrincipal { } 

lone sig Alice extends WebPrincipal {}
lone sig Mallory extends WEBATTACKER {}


sig Origin {
//	port: Port, 
	schema: Schema,
	dnslabel : DNS,
}


abstract sig certificateAuthority{}
one sig BADCA,GOODCA extends certificateAuthority{}

sig Certificate {
	ca : certificateAuthority,
	cn : DNS,
	ne : NetworkEndpoint
}{

	//GoodCAVerifiesNonTrivialDNSValues
	ca in GOODCA and cn.parent != DNSRoot implies 
			some p:Principal | {
				cn in p.dnslabels
				ne in p.servers
				ne in cn.resolvesTo
			}
}


/****************************
Cookie Stuff
****************************/




// Currently the String type is taken but not yet implemented in Alloy
// We will replace String1 with String when the latter is fully available in Alloy
sig String1 {} 

sig UserToken extends Secret {
        id : WebPrincipal
}

sig Cookie extends Secret {
	name : Token,
	value : Token,
	domain : DNS,
	path : Path,
}{}

sig SecureCookie extends Cookie {}

sig CookieHeader extends HTTPRequestHeader{ thecookie : Cookie }
sig SetCookieHeader extends HTTPResponseHeader{	thecookie : Cookie }

fact SecureCookiesOnlySentOverHTTPS{
		all e:HTTPEvent,c:SecureCookie | {
				e.from in Browser + NormalPrincipal.servers
				httpPacketHasCookie[c,e]
		} implies e.host.schema=HTTPS

}


fact CookiesAreSameOriginAndSomeOneToldThemToTheClient{
	all areq:HTTPRequest |{ 
			areq.from in Browser  
			some ( areq.headers & CookieHeader)
	} implies  all acookie :(areq.headers & CookieHeader).thecookie | some aresp: location.(areq.from).transactions.resp | {
				//don't do same origin check as http cookies can go over https
				aresp.host.dnslabel = areq.host.dnslabel
				acookie in (aresp.headers & SetCookieHeader).thecookie
				happensBeforeOrdering[aresp,areq]
	}
}

pred httpPacketHasCookie[c:Cookie,httpevent:HTTPRequest+HTTPResponse]{
				(httpevent in HTTPRequest and  c in (httpevent.headers & CookieHeader).thecookie ) or
				(httpevent in HTTPResponse and c in (httpevent.headers & SetCookieHeader).thecookie)
}

pred hasKnowledgeViaUnencryptedHTTPEvent[c: Cookie, ne : NetworkEndpoint, usageEvent: Event]{
		ne !in WebPrincipal.servers + Browser
		some httpevent : HTTPEvent | {
			happensBeforeOrdering[httpevent,usageEvent]
			httpevent.host.schema = HTTP
			httpPacketHasCookie[c,httpevent]
		}
}

pred hasKnowledgeViaDirectHTTP[c:Cookie,ne:NetworkEndpoint,usageEvent:Event]{
		some t: HTTPTransaction | {
		happensBeforeOrdering[t.req,usageEvent]
		httpPacketHasCookie[c,t.req]
		t.resp.from = ne
	} or {
		happensBeforeOrdering[t.resp,usageEvent]
		httpPacketHasCookie[c,t.resp]
		some ((transactions.t).location & ne)
		}
}

pred hasKnowledgeCookie[c:Cookie,ne:NetworkEndpoint,usageEvent:Event]{
	ne in c.madeBy.servers or hasKnowledgeViaUnencryptedHTTPEvent[c,ne,usageEvent] or hasKnowledgeViaDirectHTTP[c,ne,usageEvent]
}

fact BeforeUsingCookieYouNeedToKnowAboutIt{
	all e:HTTPRequest + HTTPResponse | 
// Use httpPacketHasCookie
			all c:(e.(HTTPRequest <: headers) & CookieHeader).thecookie + (e.(HTTPResponse <: headers) & SetCookieHeader).thecookie |
					hasKnowledgeCookie[c,e.from,e]
}

fact NormalPrincipalsOnlyUseCookiesTheyMade{
	all e:HTTPResponse |
		all c:(e.headers & SetCookieHeader).thecookie | {
			e.from in NormalPrincipal.servers implies c.madeBy = e.from[servers]
		}
}

fact NormalPrincipalsDontReuseCookies{
	all p:NormalPrincipal | no disj e1,e2:HTTPResponse | {
			(e1.from + e2.from) in p.servers 
			some ( 	(e1.headers & SetCookieHeader).thecookie & (e2.headers & SetCookieHeader).thecookie )
	}
}

run show2 {
	some (SetCookieHeader).thecookie
} for 6
/***********************

HTTP Facts

************************/


fact scriptContextsAreSane {
	all disj sc,sc':ScriptContext | no (sc.transactions & sc'.transactions)
	all t:HTTPTransaction | t.req.from in Browser implies t in ScriptContext.transactions
}


fact HTTPTransactionsAreSane {
	all disj t,t':HTTPTransaction | no (t.resp & t'.resp ) and no (t.req & t'.req)
}





/**************************** 

HTTPServer Definitions 

****************************/

lone sig ACTIVEATTACKER extends Principal{}

//Passive Principals match their http / network parts
abstract sig PassivePrincipal extends Principal{}{
	servers in HTTPConformist
}

lone sig PASSIVEATTACKER extends PassivePrincipal{}
sig WebPrincipal extends PassivePrincipal {
  httpClients : set HTTPClient
} { httpClients.owner = this }

//HTTPAdherent so that it can make requests too
lone sig WEBATTACKER extends WebPrincipal{}

abstract sig NormalPrincipal extends WebPrincipal{} { 	dnslabels.resolvesTo in servers}
lone sig GOOD extends NormalPrincipal{}
lone sig SECURE extends NormalPrincipal{}
lone sig ORIGINAWARE extends NormalPrincipal{}

fact NonActiveFollowHTTPRules {
// Old rule was :
//	all t:HTTPTransaction | t.resp.from in HTTPServer implies t.req.host.server = t.resp.from
// We rewrite to say HTTPAdherents cant spoof from part ... here we don't say anything about principal
	all httpresponse:HTTPResponse | httpresponse.from in HTTPConformist implies httpresponse.from in httpresponse.host.dnslabel.resolvesTo
}

fact SecureIsHTTPSOnly {
// Add to this the fact that transaction schema is consistent
	all httpevent:HTTPEvent | httpevent.from in SECURE.servers implies httpevent.host.schema = HTTPS
//	STS Requirement : all sc : ScriptContext | some (getPrincipalFromOrigin[sc.owner] & SECURE ) implies sc.transactions.req.host.schema=HTTPS
}


fact CSRFProtection {
	all aResp:HTTPResponse | aResp.from in ORIGINAWARE.servers and aResp.statusCode=c200 implies {
		(resp.aResp).req.method in safeMethods or (
		let theoriginchain = ((resp.aResp).req.headers & OriginHeader).theorigin |
			some theoriginchain and theoriginchain.dnslabel in ORIGINAWARE.dnslabels
		)
	}
}

fact NormalPrincipalsHaveNonTrivialDNSValues {
// Normal Principals don't mess around with trivial DNS values
   DNSRoot !in NormalPrincipal.dnslabels.parent
}

fact WebPrincipalsObeyTheHostHeader {
	all aResp:HTTPResponse | 
		let p = servers.(aResp.from) |
			p in WebPrincipal implies {
				//the host header a NormalPrincipal Sets is always with the DNSLabels it owns
				aResp.host.dnslabel in p.dnslabels
				// it also makes sure that the from server is the same one that the dnslabel resolvesTo
				aResp.from in aResp.host.dnslabel.resolvesTo

				//additionally it responds to some request and keep semantics similar to the way Browsers keep them
				some t:HTTPTransaction | t.resp = aResp and t.req.host.dnslabel = t.resp.host.dnslabel and t.req.host.schema = t.resp.host.schema
			}
}

fact NormalPrincipalsDontMakeRequests {
	no aReq:HTTPRequest | aReq.from in NormalPrincipal.servers 
}

/***********************************

Client Definitions

************************************/



// Each user is associated with a set of network locations
// from where they use their credentials
pred isAuthorizedAccess[user:WebPrincipal, loc:NetworkEndpoint]{
  loc in user.httpClients
}

fun smartClient[]:set Browser {
  Firefox3 + InternetExplorer8 
}

// Ideally want tp use the old Principals thing


/*
one sig Accept extends HTTPRequestHeader{}
one sig AcceptCharset extends HTTPRequestHeader{}
one sig AcceptEncoding extends HTTPRequestHeader{}
one sig AcceptLanguage extends HTTPRequestHeader{}
one sig AcceptRanges extends HTTPRequestHeader{}
one sig Authorization extends HTTPRequestHeader{}
one sig CacheControl_Req extends HTTPRequestHeader{}
one sig Connection extends HTTPRequestHeader{}
one sig Cookie extends HTTPRequestHeader{}
one sig ContentLength_Req extends HTTPRequestHeader{}
one sig ContentType_Req extends HTTPRequestHeader{}
one sig Date_Req extends HTTPRequestHeader{}
one sig Expect extends HTTPRequestHeader{}
one sig From extends HTTPRequestHeader{}
one sig Host extends HTTPRequestHeader{}
one sig IfMatch extends HTTPRequestHeader{}
one sig IfModifiedSince extends HTTPRequestHeader{}
one sig IfNoneMatch extends HTTPRequestHeader{}
one sig IfRange extends HTTPRequestHeader{}
one sig IfUnmodifiedSince extends HTTPRequestHeader{}
one sig MaxForwards extends HTTPRequestHeader{}
one sig Pragma_Req extends HTTPRequestHeader{}
one sig ProxyAuthorization extends HTTPRequestHeader{}
one sig Range extends HTTPRequestHeader{}
one sig Referer extends HTTPRequestHeader{}
one sig TE extends HTTPRequestHeader{}
one sig Upgrade extends HTTPRequestHeader{}
one sig UserAgent extends HTTPRequestHeader{}
one sig Via_Req extends HTTPRequestHeader{}
one sig Warn extends HTTPRequestHeader{}


// one as right now we don't have any value in them
one sig Age extends HTTPResponseHeader{}
one sig Allow extends HTTPResponseHeader{}
one sig CacheControl_Resp extends HTTPResponseHeader{}
one sig ContentEncoding extends HTTPResponseHeader{}
one sig ContentLanguage extends HTTPResponseHeader{}
one sig ContentLength_Resp extends HTTPResponseHeader{}
one sig ContentLocation extends HTTPResponseHeader{}
one sig ContentDisposition extends HTTPResponseHeader{}
one sig ContentMD5 extends HTTPResponseHeader{}
one sig ContentRange extends HTTPResponseHeader{}
one sig ContentType_Resp extends HTTPResponseHeader{}
one sig Date_Resp extends HTTPResponseHeader{}
one sig ETag extends HTTPResponseHeader{}
one sig Expires extends HTTPResponseHeader{}
one sig LastModified extends HTTPResponseHeader{}
one sig Pragma_Resp extends HTTPResponseHeader{}
one sig ProxyAuthenticate extends HTTPResponseHeader{}
one sig RetryAfter extends HTTPResponseHeader{}
one sig Server extends HTTPResponseHeader{}

one sig Trailer extends HTTPResponseHeader{}
one sig TransferEncoding extends HTTPResponseHeader{}
one sig Vary extends HTTPResponseHeader{}
one sig Via_Resp extends HTTPResponseHeader{}
one sig Warning extends HTTPResponseHeader{}


pred WWWAuthnHeaderExists {
  some WWWAuthnHeader
}
run WWWAuthnHeaderExists for 6

fact allowedXMLHTTPRequestHeaders{
	all xhr:XMLHTTPRequest |
		no xhr.headers & (      AcceptCharset +
                                AcceptEncoding +
                                Connection +
                                ContentLength_Req +
                                Cookie +
//                                ContentTransferEncoding +
                                Date_Req +
                                Expect +
                                Host +
//                                KeepAlive +
                                Referer +
                                TE +
//                                Trailer +
//                                TransferEncoding +
                                Upgrade +
                                UserAgent +
                                Via_Req
						)

}

*/

sig WWWAuthnHeader extends HTTPResponseHeader{}{
  all resp:HTTPResponse| (some (WWWAuthnHeader & resp.headers)) => resp.statusCode=c401
}


// each user has at most one password
sig UserPassword extends UserToken { }

// sig AliceUserPassword extends UserPassword {} {id = Alice and madeBy in Alice }

pred somePasswordExists {
  some UserPassword //|p.madeBy in Alice
}

run somePasswordExists for 8


pred basicModelIsConsistent {
  some ScriptContext
  some t1:HTTPTransaction |{
    some (t1.req.from & Browser ) and
    some (t1.resp)
  }
}
run basicModelIsConsistent  for 8 but 3 HTTPResponse//, 3 HTTPRequest, 


/* 
run basicModelIsConsistent  for 8 but 3 HTTPResponse//, 3 HTTPRequest, 
   Solver=sat4j Bitwidth=4 MaxSeq=7 SkolemDepth=1 Symmetry=20
   Generating CNF...
   Generating the solution...
   Begin solveAll()
   81822 vars. 3817 primary vars. 162551 clauses. 125541ms.
   Solving...
   End solveAll()
   . found. Predicate is consistent. 1009ms.
*/ 

// run findBasicModelInstance  for 6  but 2 HTTPResponse, 
//2 HTTPRequest, 2 RequestAPI, 0 GOOD, 0 SECURE ,2 Secret, 0 String1
//1 ACTIVEATTACKER, 1 WEBATTACKER, 1 ORIGINAWARE, 
//, 2  Origin,   

