open declarations


/************************************
* CORS
*
************************************/
sig PreFlightRequest extends HTTPRequest {}{
	method = OPTIONS
	some headers & AccessControlRequestMethod
	some headers & OriginHeader
	some headers & AccessControlRequestHeaders
}

fact PreFlightIsAlwaysCrossOrigin{
	all pfr:PreFlightRequest | isCrossOriginRequest[pfr]
}

abstract sig CORSResponseHeader extends HTTPResponseHeader{}
sig AccessControlAllowOrigin extends CORSResponseHeader {origin: Origin}
sig AccessControlAllowMethods extends CORSResponseHeader {allowedMethods : set Method}
sig AccessControlAllowHeaders extends CORSResponseHeader {allowedHeaders : set HTTPRequestHeader}
sig AccessControlMaxAge,AccessControlAllowCredentials extends CORSResponseHeader{}


abstract sig CORSRequestHeader extends HTTPRequestHeader{}
sig AccessControlRequestMethod extends CORSRequestHeader {requestedMethod : Method}
sig AccessControlRequestHeaders extends CORSRequestHeader {requestedHeaders : set HTTPRequestHeader}

run show {} for 6

/* Execution result:
Executing "Run show for 6"
   Solver=sat4j Bitwidth=4 MaxSeq=6 SkolemDepth=1 Symmetry=20
   32458 vars. 1798 primary vars. 65424 clauses. 52047ms.
   Instance found. Predicate is consistent. 201ms.
*/
