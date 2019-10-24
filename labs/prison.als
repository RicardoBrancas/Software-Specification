module exercises/prison

sig Gang {
	members: set Inmate
}

sig Inmate {
	room: Cell
}

sig Cell {}

pred safe () {
	all i, i' : Inmate | (#members.i > 0 and #members.i' > 0 and members.i != members.i') => i.room != i'.room
}

pred happy () {
	all i, i' : Inmate | i.room = i'.room => members.i = members.i'
}

assert safeIsHappy {
	safe => happy
}

check safeIsHappy for 5

pred show () {
	safe
	
}

run show
