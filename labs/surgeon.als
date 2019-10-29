module surgeon

open util/ordering[Time]
open util/boolean

sig Time {}

sig Patient {
	operated: Bool -> Time
} {
	all t: Time-last | let t' = t.next | operated.t = True => operated.t' = True
}

one sig Surgeon {
	left: (seq Glove) -> Time,
	right: (seq Glove) -> Time
} {
	all t: Time | not (left + right).t.hasDups
}

sig Glove {
	mainSide : Bool -> Time,
	reverseSide :Bool -> Time,
}

abstract sig Event {
	pre, post: Time
}

sig PutGloveRight extends Event {
	glove: Glove,
} {	
	// pre-conditions
	not glove in Surgeon.(left+right).pre.elems
	Surgeon.right.pre.isEmpty => no glove.reverseSide.pre

	// post-conditions
	Surgeon.right.post = Surgeon.right.pre.add [glove]
	glove.reverseSide.post = glove.reverseSide.pre + Surgeon.right.pre.last.mainSide.pre
	Surgeon.right.pre.last.mainSide.post = Surgeon.right.pre.last.mainSide.pre +  glove.reverseSide.pre

	// frame conditions
	noGloveChangeExceptAdding [glove]
	noOperatedChangeExcept [none]
	noContaminantChangeExcept [none, none]
}

sig PutGloveLeft extends Event {
	glove: Glove,
} {	
	// pre-conditions
	not glove in Surgeon.(left+right).pre.elems
	Surgeon.left.pre.isEmpty => no glove.reverseSide.pre

	// post-conditions
	Surgeon.left.post = Surgeon.left.pre.add [glove]
	glove.reverseSide.post = glove.reverseSide.pre + Surgeon.left.pre.last.mainSide.pre
	Surgeon.left.pre.last.mainSide.post = Surgeon.left.pre.last.mainSide.pre +  glove.reverseSide.pre

	// frame conditions
	noGloveChangeExceptAdding [glove]
	noOperatedChangeExcept [none]
	noContaminantChangeExcept [none, none]
}

sig TakeGloveRight extends Event {} {
	// pre-conditions
	some Surgeon.right.pre.elems

	// post-conditions
	Surgeon.right.post = Surgeon.right.pre.butlast
	
	// frame conditions
	noGloveChangeExceptRemoving
	noOperatedChangeExcept [none]
	noContaminantChangeExcept [none, none]
}

sig TakeGloveLeft extends Event {} {
	// pre-conditions
	some Surgeon.left.pre.elems

	// post-conditions
	Surgeon.left.post = Surgeon.left.pre.butlast
	
	// frame conditions
	noGloveChangeExceptRemoving
	noOperatedChangeExcept [none]
	noContaminantChangeExcept [none, none]
}

sig Operating extends Event {
	patient: Patient
} {
	// pre-conditions
	patient.operated.pre = False
	some Surgeon.(left+right).pre.elems // surgeon must be wearing gloves
	Surgeon.(left+right).pre.last.mainSide.pre = False // glove should not be contaminated

	// post-conditions
	patient.operated.post = True
	Surgeon.(left+right).post.last.mainSide.post = True // patient contaminates glove
	
	// frame conditions
	noGloveChange
	noOperatedChangeExcept [patient]
	noContaminantChangeExcept [Surgeon.(left+right).post.last, patient]
}

sig Reverse extends Event {
	g: Glove
} {
	// pre-conditions
	g not in Surgeon.(left+right).pre.elems
	
	// post-conditions
	g.mainSide.post = g.reverseSide.pre
	g.reverseSide.post = g.mainSide.pre
	
	// frame conditions
	noGloveChange
	noOperatedChangeExcept [none]
	noContaminantChangeExceptG [Surgeon.(left+right).post.last]
}

pred init (t: Time) {
	no Surgeon.(left+right).t
	all p: Patient | p.operated.t = False
	all g: Glove | g.(reverseSide + mainSide).t = False
}

pred Event.noOperatedChangeExcept (p: Patient) {
	(Patient - p).operated.(this.post) = (Patient -p).operated.(this.pre)
}

pred Event.noGloveChangeExceptAdding (g: Glove) {
	Surgeon.(left+right).(this.post).butlast = Surgeon.(left+right).(this.pre)
	Surgeon.(left+right).(this.post).elems - Surgeon.(left+right).(this.pre).elems = g
}

pred Event.noGloveChange {
	Surgeon.(left+right).(this.post) = Surgeon.(left+right).(this.pre)
}

pred Event.noGloveChangeExceptRemoving {
	Surgeon.(left+right).(this.post) = Surgeon.(left+right).(this.pre).butlast
}

pred Event.noContaminantChangeExcept (g: Glove, p: Patient) {
	all g': Glove - g | g'.mainSide.(this.post) = g'.mainSide.(this.pre)
	all g': Glove | g'.reverseSide.(this.post) = g'.reverseSide.(this.pre)
	g.mainSide.(this.pre) in g.mainSide.(this.post)
	g.mainSide.(this.post) in g.mainSide.(this.pre) + p
}

pred Event.noContaminantChangeExceptG (g: Glove) {
	all g': Glove - g | g'.mainSide.(this.post) = g'.mainSide.(this.pre)
	                    and g'.reverseSide.(this.post) = g'.reverseSide.(this.pre)
}


fact Traces {
	first.init
	all t: Time - last | let t' = t.next | some e: Event {
		e.pre = t and e.post = t'
	}
}

run {
	all p: Patient | p.operated.last = True
} for 15 but exactly 4 Glove, exactly 3 Patient
