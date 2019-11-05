open util/ordering[Time]

sig Time {}

sig Nonce {}

abstract sig MsgType {}
one sig Msg1, Msg2 extends MsgType {}

fact enoughMessageElements {
	//#Nonce >= #Time //1, 3
	//#Enc >= #Time
}

abstract sig Agent {
	keys: Agent -> Key
}

fact keysAreSymmetric {
	all a, a' : Agent | keys [a, a'] = keys [a', a] and
                        a != a' => one keys [a, a'] else no keys [a, a']
}

fact keysAreUnique {
	all a, b, a', b' : Agent | (a != a' and a' != b' and b != a') => keys [a, b] != keys [a', b']
}

sig Honest extends Agent {
	sent: Agent -> Nonce -> MsgType -> Time,
	received: Agent -> Nonce -> MsgType -> Time
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
	all h: Honest | no h.(sent+received).t  //1, 3
	some Intruder.nonces.t //2, 9
	some Intruder.encs.t //9
	//TODO: the intruder also knows some keys????
}

pred noSentExcept [pre, post: Time, h: Honest, a: Agent, n: Nonce] {
	all h': Honest - h | h'.sent.post = h'.sent.pre
	h.sent.post - (a -> n -> univ) = h.sent.pre
}

pred noReceivedExceptAdding [pre, post: Time, h: Honest, a: Agent, n: Nonce] {
	all h': Honest - h | h'.received.post = h'.received.pre
	h.received.post - (a -> n -> univ) = h.received.pre
}

pred noReceivedExceptRemoving [pre, post: Time, h: Honest, a: Agent, n: Nonce] {
	all h': Honest - h | h'.received.post = h'.received.pre
	h.received.post = h.received.pre - (a -> n -> univ)
}

pred noMessagesChangeExcept [pre, post: Time, m: Enc] {
	Intruder.encs.post - m = Intruder.encs.pre
}

pred noNoncesChangeExcept [pre, post: Time, n: Nonce] {
	Intruder.nonces.post - n = Intruder.nonces.pre
}

pred fresh (n: Nonce, t: Time) { // This ensures that nonce n is fresh at time t
	let T = t+t.prevs | all t': T | no (univ -> n -> univ) & Honest.(sent+received).t' // 1
	all m: Intruder.encs.t | m.nonce != n
}

// TODO: is a Honest or Agent??
pred msg1HonestToIntruder[pre, post: Time, a: Honest, b: Honest, n: Nonce] {
  	// pre-cond
  	fresh [n, pre] //1
  	
  	// post-cond
  	a.sent.post [b, n] = Msg1
  	n in Intruder.nonces.post

  	// frame
  	noSentExcept [pre, post, a, b, n]
  	noReceivedExceptAdding [pre, post, none, none, none]
  	noMessagesChangeExcept [pre, post, none]
	noNoncesChangeExcept [pre, post, n]
}

pred msg1IntruderToHonest[pre, post: Time, a: Honest, b: Honest, n: Nonce] {
  	// pre-cond
	n in Intruder.nonces.pre //2
  	
  	// post-cond
  	b.received.post [a, n] = Msg1

  	// frame
  	noSentExcept [pre, post, none, none, none]
  	noReceivedExceptAdding [pre, post, b, a, n]
  	noMessagesChangeExcept [pre, post, none]
	noNoncesChangeExcept [pre, post, none]
}

pred msg2HonestToIntruder[pre, post: Time, a: Honest, b: Honest, n: Nonce, m: Enc] {
	// pre-cond
	fresh [n, pre] //3
	m.id = b //FIX
	a.(b.received.pre) [m.nonce] = Msg1
	m.key = keys [b, a]

	// post-cond
	b.sent.post [a, n] = Msg2
	m in Intruder.encs.post
	n in Intruder.nonces.post
	no a.(b.received.post) [m.nonce]

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
	b.(a.sent.pre) [m.nonce] = Msg1
	m.id = b //FIX

	// post-cond
	a.received.post [b, n] = Msg2
		
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
	b.(a.received.pre) [m.nonce] = Msg2

	// post-cond
	m in Intruder.encs.post
	no b.(a.received.post) [m.nonce]

	// frame
	noSentExcept [pre, post, none, none, none]
  	noReceivedExceptRemoving [pre, post, a, b, m.nonce]
  	noMessagesChangeExcept [pre, post, m]
	noNoncesChangeExcept [pre, post, none]
}

pred msg3IntruderToHonest[pre, post: Time, a: Honest, b: Honest, m: Enc] {
	// pre-cond
	m in Intruder.encs.pre //TODO: can the intruder fabricate encoded messages?
	m.key = keys [a, b]
	a.(b.sent.pre) [m.nonce] = Msg2
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

//10:
pred sequence_messages[t:Time, h1: Honest, h2: Honest, n,n':Nonce, m,m': Enc] {
	let t1= t.next,t2= t1.next, t3= t2.next, t4= t3.next , 
	t5= t4.next ,t6= t5.next |
	msg1HonestToIntruder[t,t1,h1,h2,n] and 
	msg1IntruderToHonest[t1,t2, h1, h2,n ] and
	msg2HonestToIntruder[t2,t3, h1,h2,n',m ] and
	msg2IntruderToHonest[t3,t4, h1, h2,n',m ] and
	msg3HonestToIntruder[t4,t5, h1, h2,m' ] and
	msg3IntruderToHonest[t5,t6, h1, h2,m' ]
}
run sequence_messages for 7 but exactly 2 Honest

//11:
assert a_autenticate_b{
	all t: Time, a, b:Honest, n:Nonce, m:Enc | let t' = t.next | 
	msg2IntruderToHonest[t, t', a, b, n, m] => 
	((some t'': t.prevs, n': Nonce | let t''' = t''.next | msg2HonestToIntruder[t'', t''', a, b, n', m])
	or
	(some t_prev: t.prevs | let t_prev' = t_prev.next | msg3HonestToIntruder [t_prev, t_prev', b, a, m]))
}
check a_autenticate_b for 8

//12:
assert b_autenticate_a {
	all t: Time, a, b: Honest, m: Enc | let t' = t.next |
	msg3IntruderToHonest [t, t', a, b, m] =>
	((some t_prev: t.prevs | let t_prev' = t_prev.next | msg3HonestToIntruder [t_prev, t_prev', a, b, m])
	or
	(some t_prev: t.prevs, n: Nonce | let t_prev' = t_prev.next | msg2HonestToIntruder [t_prev, t_prev', b, a, n, m]))
}
check b_autenticate_a for 7

//13:
assert someone_ini_protocol {
	all t: Time, a, b:Honest, m:Enc | let t' = t.next |
	msg3HonestToIntruder[t, t', a, b, m] =>
	(some t'': t.prevs, n: Nonce | let t''' = t''.next |
		(msg1HonestToIntruder[t'', t''', a, b, n] ||
		 msg1HonestToIntruder[t'', t''', b, a, n])
	)
}
check someone_ini_protocol for 8

run {
} for 7 but 2 Honest




