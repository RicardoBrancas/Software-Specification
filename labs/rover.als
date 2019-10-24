open util/ordering[Time] as T
open util/ordering[Coor] as C

sig Time {}
sig Coor {}

sig Position {x, y: Coor }

abstract sig Direction {}
one sig North, South, East, West extends Direction {}

sig Rover {
	dir: Direction one -> Time,
	pos: Position one -> Time
}

pred turn_right [t, t':Time, rov: Rover] {
	// pre-conditions
	// post-conditions
	rov.dir.t' = next_dir_right[rov.dir.t]
	// frame-conditions
	no_dir_changes_e
}

pred go [t, t':Time, rov: Rover] {
	let np = next_pos[rov.pos.t, rov.dir.t] | {
		some np
		rov.pos.t' = np
	}
}

pred init [t:Time] {
	pos.t in Rover lone-> Position
	all disj r1, r2: Rover | no r1.pos.t & r2.pos.t
}

pred transitions {
	all t: Time - T/last | let t' = T/next[t] | some r: Rover



fact {
	all t: Time | pos.t in Rover lone->position
}

fact {
	all t: Time - T/last, r: Rover | let t' = t.next |
		r.pos.t = r.pos.t' || one_step[r.pos.t, r.pos.t']
}

fact {
	all t: Time - T/last, disj r1, r2: Rover |
		let t' = t.next | r1.pos.t' not in r2.pos.t}

run {} for 3 but 7 Time, 10 Position
