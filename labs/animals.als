
sig Animals {
	species: set Species,
	habitat: set Habitats,
	coexist: set Animals
}

sig Species {

}

sig Habitats {
	coordinator: set Veterinaries,
	veterinaries: set Veterinaries
}

sig Veterinaries {
	knowscure: set Species
}

fact animalSingleSpecies {
	all a: Animals | #a.species = 1
}

fact animalAtMostSingleHabitat {
	all a: Animals | #a.habitat <= 1
}

fact habitatAtLeastOne {
	all h: Habitats | #habitat.h >= 1
}

fact habitatAtMostHundred {
	all h: Habitats | #habitat.h <= 100
	#Habitats >= 1
}

fact habitatsCoexist {
	all h: Habitats, a, a': Animals | h in a.habitat and h in a'.habitat => a' in a.coexist
}

fact vetKnowsAtLeastOneCure {
	all v: Veterinaries | #v.knowscure >= 1
}

fact habitatSingleCoord {
	all h: Habitats | #h.coordinator = 1
}

fact vetAtMostOneCoord {
	all v: Veterinaries | #coordinator.v <= 1
}

fact coordIsVet {
	coordinator in veterinaries
}

fact vetKownsAllCures {
	all v: Veterinaries | habitat.(veterinaries.v).species in v.knowscure
	//all V: Veterinaries, h: Habitats, s: Species | s in (habitat.h).species && v in veterinaries.h => v->s in knowscure
}

fact vetAtMostTwoHabitats {
	all v: Veterinaries | #veterinaries.v <= 2
}

run {} for 8 but 8 int
