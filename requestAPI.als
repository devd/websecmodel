open declarations

/************************************
* RequestAPI
*
************************************/



lone sig FormElement extends RequestAPI {}
sig XMLHTTPRequest extends RequestAPI {	headers: set HTTPRequestHeader}

sig XMLHTTPRequest2 extends RequestAPI {
	headers: set HTTPRequestHeader
}

sig XDomainRequest extends RequestAPI {}
