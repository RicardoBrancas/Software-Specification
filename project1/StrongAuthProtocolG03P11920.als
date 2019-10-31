open util/ordering[Time]
open util/integer

sig Time {}

sig Nonce {}

abstract sig Agent {
	keys: Agent -> Key  //TODO: cardinality restrictions
	
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
	encs: Enc -> Time,
	nonces: Nonce -> Time
}

sig Key {
}

sig Enc {
	id: Agent, //FIX
	nonce: Nonce,
	key: Key
}

pred init (t: Time) {
	all h: Honest | no h.(sent+received).t  // 1
	some Intruder.nonces.t
}

pred noSentExcept [pre, post: Time, h: Honest, a: Agent, n: Nonce] {
	all h': Honest - h | h'.sent.post = h'.sent.pre
	h.sent.post - (a -> n) = h.sent.pre
}

pred noReceivedExceptAdding [pre, post: Time, h: Honest, a: Agent, n: Nonce] {
	all h': Honest - h | h'.received.post = h'.received.pre
	h.received.post - (a -> n) = h.received.pre
}

pred noReceivedExceptRemoving [pre, post: Time, h: Honest, a: Agent, n: Nonce] {
	all h': Honest - h | h'.received.post = h'.received.pre
	h.received.post = h.received.pre - (a -> n)
}

pred noMessagesChangeExcept [pre, post: Time, m: Enc] {
	Intruder.encs.post - m = Intruder.encs.pre
}

pred noNoncesChangeExcept [pre, post: Time, n: Nonce] {
	Intruder.nonces.post - n = Intruder.nonces.pre
}

pred fresh (n: Nonce, t: Time) { // This ensures that nonce n is fresh at time t
	let T = t+t.prevs | no Honest.(sent+received).T.n // 1
}

// TODO: is a Honest or Agent??
pred msg1HonestToIntruder[pre, post: Time, a: Honest, b: Honest, n: Nonce] {
  	// pre-cond
  	fresh [n, pre] // 1
  	
  	// post-cond
  	(b -> n) in a.sent.post
  	n in Intruder.nonces.post

  	// frame
  	noSentExcept [pre, post, a, b, n]
  	noReceivedExceptAdding [pre, post, none, none, none]
  	noMessagesChangeExcept [pre, post, none]
	noNoncesChangeExcept [pre, post, n]
}

pred msg1IntruderToHonest[pre, post: Time, a: Honest, b: Honest, n: Nonce] {
  	// pre-cond
	n in Intruder.nonces.pre
  	
  	// post-cond
  	(a -> n) in b.received.post

  	// frame
  	noSentExcept [pre, post, none, none, none]
  	noReceivedExceptAdding [pre, post, b, a, n]
  	noMessagesChangeExcept [pre, post, none]
	noNoncesChangeExcept [pre, post, none]

}

pred msg2HonestToIntruder[pre, post: Time, a: Honest, b: Honest, n: Nonce, m: Enc] {
	// pre-cond
	fresh [n, pre]
	m.id = b //FIX
	m.nonce in a.(b.received.pre)
	m.key = keys [b, a]

	// post-cond
	(a -> n) in b.sent.post
	m in Intruder.encs.post
	n in Intruder.nonces.post
	m.nonce not in a.(b.received.post)

	// frame
	noSentExcept [pre, post, b, a, n]
  	noReceivedExceptRemoving [pre, post, b, a, m.nonce]
  	noMessagesChangeExcept [pre, post, m]
	noNoncesChangeExcept [pre, post, n]
}

pred msg2IntruderToHonest[pre, post: Time, a: Honest, b: Honest, n: Nonce, m: Enc] {
	// pre-cond - intruder
	n in Intruder.nonces.pre
	m in Intruder.encs.pre //TODO: can the intruder fabricate encoded messages?
	// pre-cond - alice
	m.key = keys [a, b]
	m.nonce in b.(a.sent.pre)
	m.id = b //FIX

	// post-cond
	(b -> n) in a.received.post
		
	// frame
	noSentExcept [pre, post, none, none, none]
  	noReceivedExceptAdding [pre, post, a, b, n]
  	noMessagesChangeExcept [pre, post, none]
	noNoncesChangeExcept [pre, post, none]
}

pred msg3HonestToIntruder[pre, post: Time, a: Honest, b: Honest, m: Enc] {
	// pre-cond
	m.key = keys [a, b]
	m.id = a //FIX
	m.nonce in b.(a.received.pre)

	// post-cond
	m in Intruder.encs.post
	m.nonce not in b.(a.received.post)

	// frame
	noSentExcept [pre, post, none, none, none]
  	noReceivedExceptRemoving [pre, post, a, b, m.nonce]
  	noMessagesChangeExcept [pre, post, m]
	noNoncesChangeExcept [pre, post, none]
}

pred msg3IntruderToHonest[pre, post: Time, a: Honest, b: Honest, m: Enc] {
	// pre-cond
	m.key = keys [a, b]
	m.nonce in a.(b.sent.pre)
	m.id = a //FIX

	// post-cond

	// frame
	noSentExcept [pre, post, none, none, none]
  	noReceivedExceptRemoving [pre, post, none, none, none]
  	noMessagesChangeExcept [pre, post, none]
	noNoncesChangeExcept [pre, post, none]
}

fact Traces {
	first.init
	all t: Time-last | let t' = t.next | some a : Honest, b: Honest, n: Nonce, m: Enc {
		msg1HonestToIntruder [t, t', a, b, n] or
		msg1IntruderToHonest [t, t', a, b, n] or
		msg2HonestToIntruder [t, t', a, b, n, m] or
		msg2IntruderToHonest [t, t', a, b, n, m] or
		msg3HonestToIntruder [t, t', a, b, m] or
		msg3IntruderToHonest [t, t', a, b, m]
	}
}

//Requirements

// 1
/*
	// pre-cond
  	fresh [n, pre] // 1
  	
*/
assert start_new_protocol {
  //all h: Honest |                  // h is not used
	all t: Time - last |
		some n: Nonce | fresh [n, t] //pre-cond of exch 1.1
}
check start_new_protocol for 5 but exactly 5 Nonce //DUVIDA: why do we need to specify the exact number of Nonce??



//2:
/* 
n in Intruder.nonces.pre
*/
assert accept_new_protocol {
	all t: Time - last |
		some n:Nonce | n in Intruder.nonces.t
	//Duvida: 
}
check accept_new_protocol for 5

//3: 

assert continue_protocol{
	all t: Time - last | let t' = t.next, t''= t'.next |
	some n:Nonce, m: Enc, b: Honest, a: Honest |
	(msg1HonestToIntruder[t,t', a, b,n ] &&
	msg1IntruderToHonest[t,t', a, b,n ]) => 
	( (fresh [n, t''] and
      m.id = b and //FIX 
      m.nonce in a.(b.received.t'') and
	  m.key = keys [b, a])  ||
	  (m.key = keys [a, b] and
      m.id = a and//FIX 
      m.nonce in b.(a.received.t''))) 
}

check continue_protocol for 5

//4: 
pred receive_correct_message [h1: Honest, h2: Honest, n:Nonce, m: Enc]{
	all t: Time | let t'= t.next  |  (msg2HonestToIntruder[t,t', h1,h2,n,m ] &&  msg3HonestToIntruder[t,t', h1, h2,m ]) => ( msg2IntruderToHonest[t,t', h1, h2,n,m ] ||  msg3IntruderToHonest[t,t', h1, h2,m ])
}

//5:
pred receive_message [h1: Honest, h2: Honest, n:Nonce, m: Enc]{
	all t: Time | let t'= t.next  | msg1HonestToIntruder[t,t', h1, h2,n] || msg2HonestToIntruder[t,t', h1, h2,n,m] || msg3HonestToIntruder[t,t', h1, h2,m ]
}

//6:
pred send_message [h1: Honest, h2: Honest, n:Nonce, m: Enc]{
	all t: Time | let t'= t.next  | msg1IntruderToHonest[t,t', h1, h2,n ] || msg2IntruderToHonest[t,t', h1, h2,n,m ] || msg3IntruderToHonest[t,t', h1, h2,m ]
}

//7:
//ver diferença entre assert,pred,fact 
pred initially {
	//some Intruder.first
}

//8:
pred encrypt_decrypt[k:Key, i:Intruder, e:Enc] {
	// duvida:is this okay?
	e.id = i
	e.key = k
	
	
}

//9:

pred several_sessions  {
	// duvida:
	all h:Honest | some t:Time |
	#h.sent.t > 1 //no mesmo protocolo nao manda mais q 1?, logo diferentes
				  //protocolos --> mais que 1 nounce enviado ?

}

//10:
// duvida:and da ordem as mensagens?
pred sequence_messages[h1: Honest, h2: Honest, n:Nonce, m: Enc] {
	all t: Time | let t'= t.next |
	msg1HonestToIntruder[t,t',h1,h2,n] and
	msg1IntruderToHonest[t,t', h1, h2,n ] and
	msg2HonestToIntruder[t,t', h1,h2,n,m ] and
	msg2IntruderToHonest[t,t', h1, h2,n,m ] and
	msg3HonestToIntruder[t,t', h1, h2,m ] and
	msg3IntruderToHonest[t,t', h1, h2,m ]
	
}

//11:
pred a_autenticate_b [pre,t:Time, a:Honest, b:Intruder,  n:Nonce, enc:Enc]{

	//let t' = t.next |
	//(msg2IntruderToHonest[t,t', a, b,n,enc])
	//mensagem que b envia no pre igual a enc ?? 
	 
	
	
}

//12:
pred b_autenticate_a [a:Honest, b:Honest]{
	//finish
}

//13:
pred someone_ini_protocol[a:Honest, b:Honest] {
	//finish
}




run {

} for 2




