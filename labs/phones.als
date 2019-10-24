module exercises/phones

sig Phone {
	requests: set Phone,
	connects: lone Phone,
	forward: lone Phone
}

fact invariants {
	connects in requests.*forward
	all p: Phone | (#connects.p = 0 or #p.connects = 0) and #connects.p <= 1
}

fact noLoopForward {
	all p: Phone | not p in p.forward
}

fact noLoopRequest {
	all p: Phone | not p in p.requests
}

fact hasForwardNoConnects {
	all p:Phone | #p.forward = #1 => #connects.p = 0
}

run {
	#requests >= 1
	#connects >= 1
}
