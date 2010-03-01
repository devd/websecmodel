open declarations as d
open browserFacts
open requestAPIFacts


pred isNotCookieOwnerOrClient[c:madeBy.NormalPrincipal,ne : NetworkEndpoint]{
	ne !in c.madeBy.servers
	no t:HTTPTransaction | t.resp.from in c.madeBy.servers and ne = t.req.from
}

pred SecureUsesSecureCookies {
	all e:HTTPResponse | 
		all c:(e.headers & SetCookieHeader).thecookie |
					e.from in SECURE.servers implies c in SecureCookie
}

pred CorrectSTSRequirement {
	all t : ScriptContext.transactions | some (getPrincipalFromOrigin[t.req.host]  &SECURE) implies correctHTTPSTransaction[t] //implies HTTPS
}

pred noDNSRebinding {
	all p:Principal | no d:DNS | d in p.dnslabels and d.resolvesTo !in p.servers
}


fact principalsOnlyTrustThemselves{
	all p:Principal, response:p.servers[from] | (response.headers & AccessControlAllowOrigin).origin.dnslabel in p.dnslabels
}


fact {
	NetworkEndpoint = Principal.servers + HTTPClient
//	all sc:ScriptContext | no disj t1,t2:sc.transactions | some ( t1.cause & t2.cause & HTTPTransaction)
//	no client:HTTPClient | client in Principal.servers
//	all t1,t2:HTTPTransaction | t1=t2.cause implies t1+t2 in ScriptContext.transactions

	// ScriptContext only connects to DNSLabels that it knows exists/owned by some Principal
	DNS in Principal.dnslabels
}

run WebAttackerCanBeClient {
	some req:HTTPRequest | req.host.dnslabel in SECURE.dnslabels and req.from in WEBATTACKER.servers
} for 6 but exactly 2 Time

run DNSRebindingIsPossible {
	some p : Principal - SECURE | some (p.dnslabels.resolvesTo & SECURE.servers)
} for 5

run ActiveAttackerCanSpoof {
	some resp:HTTPResponse | resp.from !in resp.host.dnslabel.resolvesTo
} for 8

check NonActiveAttackerCantSpoof {
	no resp:HTTPResponse | resp.from !in resp.host.dnslabel.resolvesTo
} for 8 but exactly 0 ACTIVEATTACKER



run GoodCanBeForged{
	some t:ScriptContext.transactions | let p = getPrincipalFromOrigin[t.resp.host] | {
			some ( p & GOOD )
			t.resp.from !in p.servers
	}
	

} for 6 but exactly 1 ACTIVEATTACKER,3 Time


run SecureCanBeForged{
	some t:ScriptContext.transactions | let p = getPrincipalFromOrigin[t.resp.host] | {
			some ( p & SECURE)
			t.resp.from !in p.servers
	}
	

} for 6 but exactly 1 ACTIVEATTACKER,3 Time

check SecureCantBeForgedbyNonActive{
	no t:ScriptContext.transactions | let p = getPrincipalFromOrigin[t.resp.host] | {
			some ( p & SECURE)
			t.resp.from !in p.servers
	}
} for 8 but exactly 0 ACTIVEATTACKER//,3 Time//,0 HTTPHeader,0 RequestAPI

check HTTPSProtectsNormalPrincipals{
	no t:ScriptContext.transactions | {
			t.resp.from !in getPrincipalFromOrigin[t.resp.host].servers 
			t.resp.host.schema = HTTPS 
			some (getPrincipalFromOrigin[t.resp.host] & NormalPrincipal )
			(transactions.t).location in smartClient
	}

} for 8
			
run HTTPSDoesNotProtectOthers{
	no t:ScriptContext.transactions | t.resp.from !in getPrincipalFromOrigin[t.resp.host].servers and t.resp.host.schema = HTTPS and getPrincipalFromOrigin[t.resp.host] in NormalPrincipal 	and	(transactions.t).location in smartClient
} for 4 but exactly 3 Time


check STSProtectsSecure{
	CorrectSTSRequirement implies {
	no t:ScriptContext.transactions | let p = getPrincipalFromOrigin[t.resp.host] | {
			some ( p & SECURE)
			t.resp.from !in p.servers
			(transactions.t).location in smartClient
		}
	}
} for 8// 5 but exactly 3 Time


run PrincipalsCanControlHTTPClient {
	some (Principal.servers & HTTPClient)
} for 4


check GOODCACERTS{
	no c:Certificate |{
		c.ca = GOODCA
		c.ne !in (dnslabels.(c.cn).servers)
		c.cn.parent != DNSRoot
	}
} for 8 


check originHeaderProtectsFromCSRF{

	no t:HTTPTransaction | {
		// Transaction is in a OriginDraftConformingBrowser
		some ( (transactions.t).location & (OriginDraftConformingBrowsers))
		//Intended for an OriginAware Principal
		some getPrincipalFromOrigin[t.req.host]
		getPrincipalFromOrigin[t.req.host] in ORIGINAWARE
		// Its a non trivial request
		t.req.method in Method - safeMethods
		// The OriginAwareServer Responds
		some t.resp
		t.resp.from in ORIGINAWARE.servers
//CSRF Protection protects against only 200 responses
		t.resp.statusCode = c200

		//And the WebAttacker is involved in the causal chain

		some (WEBATTACKER.servers &	 involvedServers[t])
	}

} for 10 but 0 ACTIVEATTACKER, 1 WEBATTACKER, 1 ORIGINAWARE, 0 GOOD, 0 SECURE ,0 Secret, 1 HTTPClient//, 2 Origin, 0 PreFlightRequest, 0 CORSRequestHeader, 0 CORSResponseHeader, 0 Secret//,8 Time//, 1 RequestAPI, 0 Secret

fun involvedServers[t:HTTPTransaction]:set NetworkEndpoint{
( (t.*cause & HTTPTransaction).resp.from + getPrincipalFromOrigin[(transactions.t).owner].servers )
}


check noAttackerInvolvedDeleteToSecure{
	noDNSRebinding implies {
	no t:ScriptContext.transactions | {
		(transactions.t).location in OriginDraftConformingBrowsers
		some (getPrincipalFromOrigin[t.req.host] & SECURE)
		some ((Principal - NormalPrincipal).servers & involvedServers[t])
	    t.req.method in DELETE + PUT
	}
}
} for 6 but 0 ACTIVEATTACKER


run GoodCookiesCanLeak{
	some c:Cookie,ne:NetworkEndpoint,e:Event,sc:ScriptContext | some t:sc.transactions {
		c.madeBy in GOOD
		ne !in GOOD.servers

		httpPacketHasCookie[c,t.resp] 
		ne != sc.location
		t.resp.from in GOOD.servers
		hasKnowledgeCookie[c,ne,e]
	}
} for 6

run SecureServerCookieCanLeak{
	some sc:ScriptContext, c:Cookie,ne:NetworkEndpoint,e:Event | some t:sc.transactions {
		c.madeBy in SECURE
		ne !in SECURE.servers
		httpPacketHasCookie[c,t.resp]
		ne != t.req.from 
		t.resp.from in SECURE.servers
		// so there is ne which is not the client nor the SecureServer who has knowledge
		hasKnowledgeCookie[c,ne,e]
	}
} for 5

run SecureCookiesLeak_DumbClients{
	some sc:ScriptContext, c:SecureCookie,ne:NetworkEndpoint,e:Event | some t:sc.transactions {
		c.madeBy in SECURE
		ne !in SECURE.servers
		httpPacketHasCookie[c,t.resp]
		ne != t.req.from 
		t.resp.from in SECURE.servers
		// so there is ne which is not the client nor the SecureServer who has knowledge
		hasKnowledgeCookie[c,ne,e]
 }
} for 6//but exactly 12 Time


check SecureCookiesDontLeak_SmartClient{
	no sc:ScriptContext, c:SecureCookie,ne:NetworkEndpoint,e:Event | some t:sc.transactions {
		c.madeBy in SECURE
		ne !in SECURE.servers
		httpPacketHasCookie[c,t.resp]
		ne != t.req.from 
		t.resp.from in SECURE.servers
		// so there is ne which is not the client nor the SecureServer who has knowledge
		hasKnowledgeCookie[c,ne,e]
		sc.location in smartClient
	 }
	
} for 6


check STSMeansNoLeakageForAnyone{
	CorrectSTSRequirement implies {
	no sc:ScriptContext, c:SecureCookie,ne:NetworkEndpoint,e:Event | some t:sc.transactions {
		c.madeBy in SECURE
		ne !in SECURE.servers
		httpPacketHasCookie[c,t.resp]
		ne != t.req.from 
		t.resp.from in SECURE.servers
		// so there is ne which is not the client nor the SecureServer who has knowledge
		hasKnowledgeCookie[c,ne,e]
	//	sc.location in smartClient
	 }
  }
} for 6



fun trSchema[]:HTTPTransaction -> Schema {
(ScriptContext.transactions <: iden).req.host.schema
//~((~owner).transactions).schema
}

fun requestTo_http[]:HTTPRequest->Principal {
	d/HTTPRequest <: host.dnslabel.~dnslabels
}


fun responseFrom_http[]:HTTPResponse->Principal {
	d/HTTPResponse <: host.dnslabel.~dnslabels
}

fun scOwner[]: ScriptContext ->  Principal {
	owner.dnslabel.~dnslabels
}

fun httpreqOrigin[]:HTTPRequest -> Principal {
	(d/HTTPRequest <: headers).theorigin.dnslabel.~dnslabels
}

fun responseFrom_actual[]:HTTPResponse -> Principal {
	HTTPResponse <: from.~servers
}

fun DNSOwnedBy[]:DNS->Principal {
	~dnslabels
}

fun DNSownerServers[]:DNS->NetworkEndpoint {
		~dnslabels.servers
}
	
