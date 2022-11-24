// TODO - ask if it's needed to speciffy DSO entity
// TODO create entities to define power (or remove this concept) and replace secondsLeft with timestampEnd

sig UserId{}

sig User  {
	id: disj one UserId,
	car: one Car,
	schedules: set Schedule
}

// Car - related signatures
sig Car {
	batteryState: one BatteryState
}

abstract sig BatteryState {}
sig NEEDS_CHARGING extends BatteryState {}
sig CHARGING extends BatteryState {}
sig CHARGED extends BatteryState {}

// Defines an appointment, composed of dates and location
sig Schedule {
	startingTime: one Timestamp,
	endingTime: one Timestamp,
	location: one Location
} {
	startingTime.value < endingTime.value
}

sig Timestamp {
	// This value represents the "epoch time",
	// i.e. the number of seconds since 1st January 1970, as done in practice by many systems
	value: one Int
} {
	value > 0
}

sig Location {}

// CPO view
sig CPO {
	stations: set ChargingStation
}

sig EnergyPrice {
	basePrice: one Price,
	discount: one Price
} {
	discount.value < basePrice.value
}

sig Price {
	value: one Int
} {
	value >= 0
}

sig ChargingStation {
	location: one Location,
	chargingSocketsGroups: some ChargingSocketsGroup
}

// This sig is needed to model the availability of every tipe of charger present in the station
sig ChargingSocketsGroup {
	// FIXME: does every group in every station have a different price per kWh? In this case the entity CPO could be removed
	sockets: set ChargingSocket,
	currentEnergyPrice: one EnergyPrice,  // Expressed in €
	secondsUntilFree: one Int
} {
	secondsUntilFree >= 0
}

sig ChargingSocket {
	type: one ChargingSocketType,
	attachedCar: lone ChargingCar
}

// We assume that the maximum power erogated by each socket type is standardized and doesn't depend on
// the specific charging station
abstract sig ChargingSocketType {
	maxErogatedPower: one Int
} {
	maxErogatedPower > 0
}
one sig SLOW extends ChargingSocketType {}
one sig RAPID extends ChargingSocketType {}
one sig FAST extends ChargingSocketType {}

sig ChargingCar extends Car {
	// FIXME does powerAbsorbed have to go here or it can be left in Car?
	absorbedPower: one Int,
	secondsLeft: one Int
} {
	secondsLeft >= 0
	absorbedPower >= 0
}

sig Suggestion {
	station: one ChargingStation,
	user: one User,
	timestamp: one Timestamp
}

// Facts
fact erogatedPowerConstraint {
	FAST.maxErogatedPower > RAPID.maxErogatedPower and RAPID.maxErogatedPower > SLOW.maxErogatedPower
}

fact maxErogatedPowerSufficient {
	all group: ChargingSocketsGroup | (all sock: ChargingSocket |
		(sock in group.sockets) implies (sock.attachedCar.absorbedPower <= sock.type.maxErogatedPower)  )
}

fact everyGroupHasAUniqueStation {
	all g: ChargingSocketsGroup | (one s: ChargingStation | g in s.chargingSocketsGroups)
}

fact everySocketHasAUniqueGroup {
	all sock: ChargingSocket | (one group: ChargingSocketsGroup | sock in group.sockets)
}

fact noCarWithoutUser {
	all c: Car | (one u: User | c = u.car)
}

fact noScheduleWithoutUser {
	all s: Schedule | (one u: User | s in u.schedules)
}

fact noBatteryStateWithoutCar {
	all state: BatteryState | (one c: Car | state = c.batteryState)
}

fact noEnergyPriceWithoutGroup {
	all e: EnergyPrice | (one group: ChargingSocketsGroup | e = group.currentEnergyPrice)
}

fact noChargingStationWithoutCPO {
	all s: ChargingStation | (one cpo: CPO | s  in cpo.stations)
}

fact allSocketsInGroupHaveSameType {
	all group: ChargingSocketsGroup, socket1, socket2: ChargingSocket |
		(socket1 in group.sockets and socket2 in group.sockets) implies socket1.type = socket2.type
}

fact noTwoGroupsWithSameChargingType {
	no disjoint g1, g2: ChargingSocketsGroup | ( some disjoint s1, s2: ChargingSocket | (
		s1 in g1.sockets and s2 in g2.sockets and s1.type = s2.type) )
}

fact noEmptyGroups {
	all g: ChargingSocketsGroup | (some s: ChargingSocket | s in g.sockets)
}

fact timeUntilOneGroupSocketIsFreeIsCoherent {
	// If there's a free socket then secondsUntilFreed = 0, otherwise "secondsUntilFree" is the minimum
	// among all "secondsLeft" attributes of the charging cars
	all group: ChargingSocketsGroup | (group.secondsUntilFree = 0 iff (
		some socket: ChargingSocket | (socket in group.sockets and no c: ChargingCar | (c = socket.attachedCar) )))
	and
	all group: ChargingSocketsGroup, socket: ChargingSocket, car: ChargingCar |
		(socket in group.sockets and car = socket.attachedCar) implies group.secondsUntilFree <= car.secondsLeft
}

fact chargingCarHasCorrectType {
	// If a car is being charged, its BatteryState must be CHARGING or CHARGED - it could happen that the recharge
	// is finished but the car is still attached
	all car: ChargingCar | car.batteryState = CHARGING or car.batteryState = CHARGED
}

fact chargedCarDoesNotAbsorbePower {
	// If a car is fully charged it does not absorbe power from the socket
	all car: ChargingCar | (car.absorbedPower = 0) iff (car.batteryState = CHARGED)
}

fact suggestionPresentOnlyIfCarNeedsCharging {
	// Every suggestion has to be related to a car that needs charging
	all s: Suggestion | (s.user.car.batteryState = NEEDS_CHARGING)
}

fact eachSuggestionIsCoeherentWithUserSchedule {
	// Each suggestion is based on an appointment of the user
	all sugg: Suggestion | (some schedule: Schedule | schedule in sugg.user.schedules and
		schedule.location = sugg.location and sugg.timestamp.value <= schedule.startingTime.value )
}

// TODO this assertion could be removed because redundant - behaviour already specified while defining "id" field
assert noDuplicateIds {
	no disjoint u1, u2: User | u1.id = u2.id
}

// TODO remember: every "sub-entity" (e.g. BatteryLevel) can't exist independently (i.e. without a BatteryState). Has this to be formalized? Otherwise
// the world isn't realistic

pred chargeCar [c, c1: Car, station: ChargingStation, chosenType: ChargingSocketType] {

}

pred createSuggestionBasedOnSchedule {

}

pred createSuggestionBasedOnDiscount {

}

// With many attributes the model is not so clear, how to fix?
// What to do with Double?
// Why do some simple constraints create problems?

pred world  {
	#User >= 3
	#Schedule >= 5
}

run world for 7
