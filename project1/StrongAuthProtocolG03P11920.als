open util/ordering[Time]
open util/integer

sig Time {}

sig Nonce {}

abstract sig Agent {
	keys: Agent -> Key -> Time //TODO: cardinality restrictions
}

sig Honest extends Agent {
	sent: Agent -> Nonce -> Time, //TODO: cardinality restrictions
	received: Agent -> Nonce -> Time //TODO: cardinality restrictions
}

one sig Intruder extends Agent {}

sig Key {}

sig Enc {
	//TODO: message?
	key: Key //TODO: cardinality restrictions
}

pred init (t: Time) {
	all h: Honest | no h.(sent+received).t
}

pred fresh (n: Nonce, t: Time) { // This ensures that nonce n is fresh at time t
	all t: Time, h: Honest | let T = prevs [t] | no h.(sent+received).T.n
}

pred msg1HonestToIntruder[pre,pos: Time, a: Agent, a2: Agent, n: Nonce]{
	
}

pred msg1IntruderToHonest[pre,pos: Time, a: Agent, a2: Agent, n: Nonce]{}

pred msg2HonestToIntruder[pre,pos: Time, a: Agent, a2: Agent, n: Nonce, m: Enc]{}

pred msg2IntruderToHonest[pre,pos: Time, a: Agent, a2: Agent, n: Nonce, m: Enc]{}

pred msg3HonestToIntruder[pre,pos: Time, a: Agent, a2: Agent, m: Enc]{}

pred msg3IntruderToHonest[pre,pos: Time, a: Agent, a2: Agent, n: Nonce, m: Enc]{}

fact Traces {
	first.init
}

run {
}
