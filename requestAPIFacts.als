open requestAPI
open cors

fact FormOnlyDoesPostOrGet {
	all t:ScriptContext.transactions | t.cause in FormElement implies t.req.method in GET + POST + PUT+ DELETE
}

fact {
	all t:ScriptContext.transactions | t.cause in FormElement  and t.req.method in PUT+DELETE implies {
			not ( isCrossOriginRequest[t.req] )
			no t.(~cause)
	}
}



fact XHRNoCrossOriginRequestOrRedirect{
	all t:ScriptContext.transactions |
		t.^cause in (XMLHTTPRequest+HTTPTransaction) implies not isCrossOriginRequest[t.req]
}

fact XHR2_CrossOrigin {
	all t:ScriptContext.transactions | 
		t.^cause in (XMLHTTPRequest2+HTTPTransaction) implies { 
						CORSPreFlightRequestTransaction[t] 
						or simpleCORSTransaction[t] 
						or complexCORSTransaction[t]
						or (not isCrossOriginRequest[t.req])
					}
}

pred simpleCORSTransaction[t:HTTPTransaction]{
		isCrossOriginRequest[t.req]
		t.cause in XMLHTTPRequest2 //As simple CORS Transaction don't redirect
		t.req.method in GET + POST
}
	
pred CORSPreFlightRequestTransaction[t:HTTPTransaction]{
	t.req in PreFlightRequest
    isCrossOriginRequest[t.req]
	t.cause in XMLHTTPRequest2
	//no redirects for CORSPreflight
	t.resp.statusCode in c301+c302+c303+c307 implies no t.(~cause)
}



//Remove all preflight request requirement in this .. add that to servers, that they make such type response only for a preflightRequest
pred complexCORSTransaction[t:HTTPTransaction]{
	t.req !in PreFlightRequest
	isCrossOriginRequest[t.req]
	t.cause in XMLHTTPRequest2 // no redirect allowed
	some t1:(transactions.t).transactions | {
		CORSPreFlightRequestTransaction[t1]
		t1.req.host = t.req.host
		t1.req.path = t.req.path		
		some (t.req.method & (t1.resp.headers & AccessControlAllowMethods).allowedMethods)
		some ((transactions.t).owner.dnslabel & (t1.resp.headers & AccessControlAllowOrigin).origin.dnslabel)
	}
	t.resp.statusCode in c301+c302+c303+c307 implies no t.(~cause)
}

fact XDROnlyDoesPostOrGet {
	all t:HTTPTransaction | t.cause in XDomainRequest implies {
			t.req.method in GET + POST
			t in (location.InternetExplorer).transactions
			not (t.req.host.schema = (transactions.t).owner.schema and t.req.host.dnslabel = (transactions.t).owner.dnslabel )
	}
}


fact XDRRedirect {
	all t:HTTPTransaction | t.cause in XDomainRequest implies {
			(t.^(~cause)).req.method=GET //all transactions caused by this other than itself
			some t.(~cause) implies  { //if there is a transaction caused by this
					(t.req.method=GET and t.resp.statusCode in c301+c302+c303+c307) or  
					(t.req.method=POST and t.resp.statusCode in c301+c302+c303)
			}
	}
}

// What about how the server opts into letting XDR tell the script context about the value of the response?

run show {} for 6

/*

Executing "Run show for 6"
   Solver=sat4j Bitwidth=4 MaxSeq=6 SkolemDepth=1 Symmetry=20
   99857 vars. 2158 primary vars. 207102 clauses. 56137ms.
   Instance found. Predicate is consistent. 1596ms.

*/
