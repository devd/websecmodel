open declarations

// model basic auth login

sig BAAuthHeader extends HTTPRequestHeader{ thebaToken : UserToken }

sig BAAuthToken extends UserToken {}

pred reqHasBAToken[ req:HTTPRequest, token: BAAuthToken]{
  token in (req.headers & BAAuthHeader).thebaToken 
}

// Add multi-realm support later.
pred isLoggedInViaBA [t: HTTPTransaction ] {
   t.req.path = SENSITIVE and  some token : BAAuthToken | reqHasBAToken[t.req, token]
}



pred hasBAKnowledgeViaHTTP[token: BAAuthToken,  usageEvent: Event]{
		some baReq : HTTPRequest | {
			happensBeforeOrdering[baReq,usageEvent]
			baReq.host.schema = HTTP
			reqHasBAToken[baReq, token]
		}
}


pred hasBAKnowledgeViaDirectHTTP[token: BAAuthToken, ne:NetworkEndpoint,usageEvent:Event]{
		some t: HTTPTransaction | {
		happensBeforeOrdering[t.req,usageEvent]
		reqHasBAToken[t.req, token]
		(t.req.from = ne) or (t.req.to = ne)
	} 
}

pred hasBAKnowledge[token: BAAuthToken, ne:NetworkEndpoint,usageEvent:Event]{
  hasBAKnowledgeViaHTTP[token,usageEvent] or hasBAKnowledgeViaDirectHTTP[token,ne,usageEvent] or
  // We need at least one person who can login via Basic Auth. 
  (token.id = Alice and token.madeBy=Alice and isAuthorizedAccess[Alice,ne])
}

/*
fact someUserCanLoginViaBA {
  some t: HTTPTransaction | t.req.path = PROTECTED and some token : BAAuthToken | {
    reqHasBAToken[t.req, token]
    token.id = Alice
    t.req.from in Alice.browsers
  }
}
*/

fact BeforeUsingBATokenYouNeedToKnowAboutIt{
	all req:HTTPRequest | all token: BAAuthToken |reqHasBAToken[req, token] =>
					hasBAKnowledge[token,req.from,req]
}

// Alice's BA credential leaks to some principal beyond the endpoints of direct HTTP connection
pred baCredentialsLeakToAttackers{
  some req:HTTPRequest, token:BAAuthToken| {
    reqHasBAToken[req, token]  and 
    token.id = Alice and 
    not isAuthorizedAccess[Alice, req.from]  and 
    req.from in (PASSIVEATTACKER+ACTIVEATTACKER+WEBATTACKER).servers 
  }
}

fact BARemoveUnproductiveBranches {
  no RequestAPI
  no PassPetStore
  all  token:BAAuthToken| some  req:HTTPRequest | reqHasBAToken[req, token] 
  no LOGOUT
  no LOGIN
}

// run show {} for 6
run baCredentialsLeakToAttackers for 10 but  2 Origin, 1 BAAuthHeader,  2 Certificate//, 4 HTTPRequest, 4 HTTPResponse 

/* Result:
Executing "Run baCredentialsLeakToAttackers for 10 but  2 Origin"
   Solver=sat4j Bitwidth=4 MaxSeq=7 SkolemDepth=1 Symmetry=20
   148678 vars. 4460 primary vars. 324813 clauses. 63353ms.
   Instance found. Predicate is consistent. 5240ms.
*/
