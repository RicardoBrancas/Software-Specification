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

pred msg1HonestToIntruder[pre,pos: Time, a: Agent, a2: Agent, n: Nonce]{
	
}

pred msg1IntruderToHonest[pre,pos: Time, a: Agent, a2: Agent, n: Nonce]{}

pred msg2HonestToIntruder[pre,pos: Time, a: Agent, a2: Agent, n: Nonce, m: Enc]{}

pred msg2IntruderToHonest[pre,pos: Time, a: Agent, a2: Agent, n: Nonce, m: Enc]{}

pred msg3HonestToIntruder[pre,pos: Time, a: Agent, a2: Agent, m: Enc]{}

pred msg3IntruderToHonest[pre,pos: Time, a: Agent, a2: Agent, n: Nonce, m: Enc]{}

run {}
