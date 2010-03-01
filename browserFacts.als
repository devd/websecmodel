open declarations

// This isn't quite right.  We might need a concept of a "pure" client that isn't also a server.
fact ClientsOnlyRequest {
	all ne:NetworkEvent | ne.from in HTTPClient implies ne in HTTPRequest
}

fact BrowsersTrustGoodCAOnly{
	Browser.trustedCA = GOODCA
}

fact OriginHeaders {
	all t:ScriptContext.transactions | (transactions.t).location in OriginDraftConformingBrowsers implies {
		let t'=t.cause | {
			t' in RequestAPI implies (transactions.t).owner = (t.req.headers & OriginHeader).theorigin
			t' in HTTPTransaction implies (t.req.headers & OriginHeader).theorigin = t'.resp.host + (t'.req.headers & OriginHeader).theorigin 
		} 
	}
}

fact NoOriginByOthers {
		all t:HTTPTransaction | not( (transactions.t).location in OriginDraftConformingBrowsers )implies no (t.req.headers & OriginHeader)
}

fun OriginDraftConformingBrowsers[]:set Browser {
	Firefox+Safari+ InternetExplorer8
}

pred correctHTTPSTransaction[t:HTTPTransaction] {
			t.req.host.schema = HTTPS
			t.cert.ca in (t.req.from).trustedCA
			t.cert.cn = t.resp.host.dnslabel
			t.cert.ne = t.resp.from 
}
// smartClients don't click through errors, others do
fact browserDropsBadlyCertifiedPackets {
	all t : ScriptContext.transactions | t.req.host.schema=HTTPS and 	t.req.from in smartClient implies correctHTTPSTransaction[t]
}

run show{} for 6 but exactly 6 Time

/*************************
*
*  Redirection Behaviour of Browsers
*
**************************/

pred sameOrigin[o1:Origin , o2:Origin]{ 
	o1.schema=o2.schema and
	o1.dnslabel = o2.dnslabel
}


fact BrowserRedirectionFact {
all first,second:HTTPTransaction | first=second.cause implies {
// you are either in the same scriptcontext or you are in no particular scriptcontext
			some sc :ScriptContext | first+second in sc.transactions or no ((first+second) & ScriptContext.transactions)
			//same from is implied by same ScriptContext
			some first.resp
			happensBeforeOrdering[first.resp,second.req]
//			some (second & (transactions.first).transactions) //the second is in the same scriptContext
			first.resp.statusCode in RedirectionStatus
			second.req.host =(first.resp.headers & location).targetOrigin
			second.req.path = (first.resp.headers & location).targetPath
			let redirRelation = (transactions.first).location -> first.resp.statusCode -> first.req.method -> second.req.method | 
					sameOrigin[first.req.host,second.req.host ] implies redirRelation in BrowserRedirectionBehaviour else redirRelation in CrossOriginBrowserRedirectionBehaviour
			}
}

fun CrossOriginBrowserRedirectionBehaviour [] : Browser -> RedirectionStatus -> Method -> Method {
	BrowserRedirectionBehaviour - ( InternetExplorer -> RedirectionStatus -> OPTIONS -> Method  +
		Firefox -> c307 -> OPTIONS -> Method  + Safari -> RedirectionStatus -> OPTIONS -> Method )
}

fun BrowserRedirectionBehaviour [] : Browser -> RedirectionStatus -> Method -> Method {
	Firefox->FirefoxRedirectionBehaviour
	+ Safari -> SafariRedirectionBehaviour 
	+ InternetExplorer -> IERedirectionBehaviour

}

fun FirefoxRedirectionBehaviour [] : RedirectionStatus->Method->Method {
	(c301 + c302 + c303) ->(GET+PUT+POST+DELETE + OPTIONS)->GET +
	c304->GET->GET +
	c307->( (GET+POST +PUT + DELETE  + OPTIONS) <: iden )
}

fun SafariRedirectionBehaviour [] : RedirectionStatus->Method->Method {
	(RedirectionStatus - c304) -> (GET+DELETE+PUT+POST+OPTIONS) -> GET
}

fun IERedirectionBehaviour [] : RedirectionStatus -> Method -> Method {
	c301-> GET -> GET + (c301+c302+c303)->POST -> GET + 
	(c301+c302+c303 + c307)->( (PUT+DELETE + OPTIONS) <: iden ) +
	c307 -> POST -> POST
}
