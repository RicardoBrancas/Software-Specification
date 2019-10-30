open util/ordering[Time]
open util/integer

sig Time {}

sig Nonce {}

abstract sig Agent {
	keys: Agent -> Key -> Time //TODO: cardinality restrictions
	
}

fact keysAreSymmetric {
	all a, a' : Agent | keys [a, a'] = keys [a', a] and
                        a != a' => one keys [a, a'] else no keys [a, a']
}

fact keysAreUnique {
	all a, b, a', b' : Agent | (a != a' and a' != b' and b != a') => keys [a, b] != keys [a', b']
}

sig Honest extends Agent {
	sent: Agent -> Nonce -> Time, //TODO: cardinality restrictions
	received: Agent -> Nonce -> Time //TODO: cardinality restrictions
}

one sig Intruder extends Agent {
	msgs: msg -> Time
}

sig Key {
	keys: Key -> Time
}

abstract sig msg {}

sig msg1 extends msg {
	id: Agent,
	nonce: Nonce
}

sig msg2 extends msg {
	nonce: Nonce,
	enc: encMsg
}

sig msg3 extends msg {
	enc: encMsg
}

sig encMsg extends msg {
	id: Agent,
	nonce: Nonce,
	key: Key
}

pred init (t: Time) {
	all h: Honest | no h.(sent+received).t
}

pred noSentExcept [pre, post: Time, h: Honest, a: Agent, n: Nonce] {
	all h': Honest - h | h'.sent.post = h'.sent.pre
	h.sent.post - (a -> n) = h.sent.pre
}

pred noReceivedExcept [pre, post: Time, h: Honest, a: Agent, n: Nonce] {
	all h': Honest - h | h'.received.post = h'.received.pre
	h.received.post - (a -> n) = h.received.pre
}

pred noMessagesChangeExcept [pre, post: Time, m: msg] {
	Intruder.msgs.post - m = Intruder.msgs.pre
}

pred fresh (n: Nonce, t: Time) { // This ensures that nonce n is fresh at time t
	let T = t+t.prevs | no Honest.(sent+received).T.n
}

// TODO: is a Honest or Agent??
pred msg1HonestToIntruder[pre, post: Time, a: Honest, b: Honest, n: Nonce] {
  one m: msg1 | m.id = a and m.nonce = n and {
  	// pre-conds
  	fresh [n, pre]
  	
  	// post-conds
  	(b -> n) in a.sent.post
  	m in Intruder.msgs.post

  	// frame
  	noSentExcept [pre, post, a, b, n]
  	noReceivedExcept [pre, post, none, none, none]
  	noMessagesChangeExcept [pre, post, m]
  }
}

pred msg1IntruderToHonest[pre, post: Time, a: Honest, b: Honest, n: Nonce] {
	one m: msg1 | m.id = a and m.nonce = n and {
  		// pre-conds
  		
  	
  		// post-conds
  		(a -> n) in b.received.post

  		// frame
  		noSentExcept [pre, post, none, none, none]
  		noReceivedExcept [pre, post, b, a, n]
  		noMessagesChangeExcept [pre, post, none]
	}
}

pred msg2HonestToIntruder[pre, post: Time, a: Agent, a2: Agent, n: Nonce, m: encMsg] {}

pred msg2IntruderToHonest[pre, post: Time, a: Agent, a2: Agent, n: Nonce, m: encMsg] {}

pred msg3HonestToIntruder[pre, post: Time, a: Agent, a2: Agent, m: encMsg] {}

pred msg3IntruderToHonest[pre, post: Time, a: Agent, a2: Agent, m: encMsg] {}

fact Traces {
	first.init
	all t: Time-last | let t' = t.next | one a : Honest, b: Honest, n: Nonce {
		msg1HonestToIntruder [t, t', a, b, n] or
		msg1IntruderToHonest [t, t', a, b, n]
	}
}

//Requirements

//1: 
pred start_new_protocol [h: Honest, a: Agent, n:Nonce]{
	all t: Time | let t'= t.next |
	msg1HonestToIntruder[t,t',h,a,n]
	//Duvida: 
}
//run start_new_protocol

//2: 
pred accept_new_protocol [h1: Honest, h2: Honest, n:Nonce]{
	all t: Time | let t'= t.next | msg1IntruderToHonest[t,t', h1, h2,n ]
	//Duvida: 
}

//3: 
pred continue_protocol [h1: Honest, h2: Honest, n:Nonce, m: encMsg]{
	all t: Time | let t'= t.next |  (msg1HonestToIntruder[t,t', h1, h2,n ] && msg1IntruderToHonest[t,t', h1, h2,n ]) => ( msg2HonestToIntruder[t,t', h1, h2,n,m ] ||  msg3HonestToIntruder[t,t', h1, h2,m ])
}

//4: 
pred receive_correct_message [h1: Honest, h2: Honest, n:Nonce, m: encMsg]{
	all t: Time | let t'= t.next  |  (msg2HonestToIntruder[t,t', h1,h2,n,m ] &&  msg3HonestToIntruder[t,t', h1, h2,m ]) => ( msg2IntruderToHonest[t,t', h1, h2,n,m ] ||  msg3IntruderToHonest[t,t', h1, h2,m ])
}

//5:
pred receive_message [h1: Honest, h2: Honest, n:Nonce, m: encMsg]{
	all t: Time | let t'= t.next  | msg1HonestToIntruder[t,t', h1, h2,n] || msg2HonestToIntruder[t,t', h1, h2,n,m] || msg3HonestToIntruder[t,t', h1, h2,m ]
}

//6:
pred send_message [h1: Honest, h2: Honest, n:Nonce, m: encMsg]{
	all t: Time | let t'= t.next  | msg1IntruderToHonest[t,t', h1, h2,n ] || msg2IntruderToHonest[t,t', h1, h2,n,m ] || msg3IntruderToHonest[t,t', h1, h2,m ]
}

//7:
//ver diferença entre assert,pred,fact 
pred initially {
	//some Intruder.first
}

//8:
pred encrypt_decrypt[k:Key, i:Intruder, e:encMsg] {
	//is this okay?
	e.id = i
	e.key = k
	
	
}

//9:
// ter chave é signficado de ter protocol. Só pertence a 1 shared protocolo?
//falta time?
pred several_sessions  {
	//finish
	all t:Time - last |
	all a : Agent|(some (a.keys.t)) or (lone (a.keys.t))//some  or lone
}

//10:
pred sequence_messages {
	//finish
}

//11:
pred a_autenticate_bob {
	//finish
}

//12:
pred b_autenticate_a {
	//finish
}

//13:
pred someone_ini_protocol {
	//finish
}




run {
} for 7 but exactly 2 Honest




