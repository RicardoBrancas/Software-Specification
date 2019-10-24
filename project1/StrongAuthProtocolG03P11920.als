open util/ordering[Time]

sig Time {}

abstract sig Agent {
	keys: Agent -> Key //TODO: cardinality restrictions
}

sig Honest extends Agent {
	sent: Nonce -> Agent, //TODO: cardinality restrictions
	received: Nonce -> Agent //TODO: cardinality restrictions
}

one sig Intruder extends Agent {}

sig Key {}

sig Nonce {}

sig Enc {
	//TODO: message?
	key: Key //TODO: cardinality restrictions
}

run {}
