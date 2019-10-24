module surgeon

open util/ordering[Time]

sig Time {}

sig Patient {
}

one sig Surgeon {
	gloves: (seq Glove) -> Time,
	operated: set Patient -> Time
} {
	all t: Time | not gloves.t.hasDups
}

sig Glove {
	mainSide : set Patient -> Time,
	reverseSide : set Patient -> Time,
}

abstract sig Event {
	pre, post: Time
}

sig PutGlove extends Event {
	glove: Glove,
} {	
	// pre-conditions
	not glove in Surgeon.gloves.pre.elems
	Surgeon.gloves.pre.isEmpty => no glove.reverseSide.pre

	// post-conditions
	Surgeon.gloves.post = Surgeon.gloves.pre.add [glove]
	glove.reverseSide.post = glove.reverseSide.pre + Surgeon.gloves.pre.last.mainSide.pre
	Surgeon.gloves.pre.last.mainSide.post = Surgeon.gloves.pre.last.mainSide.pre +  glove.reverseSide.pre

	// frame conditions
	noGloveChangeExceptAdding [glove]
	noOperatedChangeExcept [none]
	noContaminantChangeExcept [none, none]
}

sig TakeGlove extends Event {} {
	// pre-conditions
	some Surgeon.gloves.pre.elems

	// post-conditions
	Surgeon.gloves.post = Surgeon.gloves.pre.butlast
	
	// frame conditions
	noGloveChangeExceptRemoving
	noOperatedChangeExcept [none]
	noContaminantChangeExcept [none, none]
}

sig Operating extends Event {
	patient: Patient
} {
	// pre-conditions
	not patient in Surgeon.operated.pre
	some Surgeon.gloves.pre.elems // surgeon must be wearing gloves
	no (Surgeon.gloves.pre.last.mainSide.pre - patient) // glove should only be contaminated by this patitent

	// post-conditions
	patient in Surgeon.operated.post
	patient in Surgeon.gloves.post.last.mainSide.post // patient contaminates glove
	
	// frame conditions
	noGloveChange
	noOperatedChangeExcept [patient]
	noContaminantChangeExcept [Surgeon.gloves.post.last, patient]
}

sig Reverse extends Event {} {
	// pre-conditions
	some Surgeon.gloves.pre
	#Surgeon.gloves.pre = 1 => no Surgeon.gloves.pre.last.mainSide // can't reverse glove that will touch surgeon
	
	// post-conditions
	Surgeon.gloves.post.last.mainSide.post = Surgeon.gloves.pre.last.reverseSide.pre
	Surgeon.gloves.post.last.reverseSide.post = Surgeon.gloves.pre.last.mainSide.pre
	Surgeon.gloves.post.butlast.last.mainSide.post = Surgeon.gloves.pre.butlast.last.mainSide.pre + Surgeon.gloves.pre.last.mainSide.pre
	
	// frame conditions
	noGloveChange
	noOperatedChangeExcept [none]
	noContaminantChangeExceptG [Surgeon.gloves.post.last]
}

pred init (t: Time) {
	no Surgeon.gloves.t
	no Surgeon.operated.t
	no mainSide.t
	no reverseSide.t
}

pred Event.noOperatedChangeExcept (p: Patient) {
	Surgeon.operated.(this.pre) in Surgeon.operated.(this.post)
	Surgeon.operated.(this.post) in Surgeon.operated.(this.pre) + p
}

pred Event.noGloveChangeExceptAdding (g: Glove) {
	Surgeon.gloves.(this.post).butlast = Surgeon.gloves.(this.pre)
	Surgeon.gloves.(this.post).elems - Surgeon.gloves.(this.pre).elems = g
}

pred Event.noGloveChange {
	Surgeon.gloves.(this.post) = Surgeon.gloves.(this.pre)
}

pred Event.noGloveChangeExceptRemoving {
	Surgeon.gloves.(this.post) = Surgeon.gloves.(this.pre).butlast
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
	Patient in Surgeon.operated.last
} for 10 but exactly 2 Glove, exactly 3 Patient
