open declarations 
open cors

abstract sig CORSIgnorantServer extends HTTPServer {}
abstract sig MuteCORSIgnorantServer extends CORSIgnorantServer {}

fact CORSIgnorantServerLacksCORSHeaders {
// we don't use resp.host , as attacker can edit that
	all resp:HTTPResponse |	resp.from=CORSIgnorantServer implies no (resp.headers & CORSResponseHeader)
	}
