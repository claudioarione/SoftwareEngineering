// TODO - ask if it's needed to speciffy DSO entity
// TODO until now I have left the Int for power values, assuming that if a user has a fast-charging car he can be shown also suggestions related to
// slow-charging sockets. Can the model be left as it is?

sig UserId{}

sig User  {
	id: disj one UserId,
	car: one Car,
	schedules: set Schedule
}

// Car - related signatures
sig Car {
	batteryState: one BatteryState,
	absorbedPower: one Int,
	chargeSecondsLeft: one Int
} {
	chargeSecondsLeft >= 0
	absorbedPower >= 0
}

abstract sig BatteryState {}
one sig NEEDS_CHARGING extends BatteryState {}
one sig CHARGING extends BatteryState {}
one sig CHARGED extends BatteryState {}

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
	// The declaration of an Int field "price", although natural, is omitted because not relevant for the model
}
sig STANDARD extends EnergyPrice {}
sig DISCOUNT extends EnergyPrice {}

sig ChargingStation {
	location: one Location,
	chargingSocketsGroups: some ChargingSocketsGroup
}

// This sig is needed to model the availability of every tipe of charger present in the station
sig ChargingSocketsGroup {
	sockets: set ChargingSocket,
	currentEnergyPrice: one EnergyPrice,
	secondsUntilFree: one Int
} {
	secondsUntilFree >= 0
}

sig ChargingSocket {
	type: one ChargingSocketType,
	attachedCar: lone Car
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

abstract sig ChargingAction {
	// We assume that a user can book a specific ChargingSocket
	socket: one ChargingSocket,
	user: one User,
	validFrom: one Timestamp,
	validUntil: one Timestamp
} {
	validFrom.value <= validUntil.value
}
sig Suggestion extends ChargingAction {}
sig Prenotation extends ChargingAction {}

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
		some socket: ChargingSocket | (socket in group.sockets and no c: Car | (c = socket.attachedCar) )))
	and
	all group: ChargingSocketsGroup, socket: ChargingSocket, car: Car |
		(socket in group.sockets and car = socket.attachedCar) implies group.secondsUntilFree <= car.chargeSecondsLeft
}

fact chargingCarHasCorrectType {
	// If a car is being charged, its BatteryState must be CHARGING or CHARGED - it could happen that the recharge
	// is finished but the car is still attached
	all socket: ChargingSocket | (socket.attachedCar != none implies socket.attachedCar.batteryState = CHARGING)
}

fact onlyChargingCarsAbsorbePower {
	all car: Car | (car.absorbedPower = 0) iff not (car.batteryState = CHARGING)
}

fact onlyChargingCarsHaveSecondsLeft {
	// If a car is fully charged it does not absorbe power from the socket
	all car: Car | (car.chargeSecondsLeft = 0) iff not (car.batteryState = CHARGING)
}

fact chargingActionPresentOnlyIfCarNeedsCharging {
	// Every charging action is related to a car that needs charging
	all action: ChargingAction | (action.user.car.batteryState = NEEDS_CHARGING)
}

fact chargingActionOnlyIfSocketFree {
	// The Prenotation or the Suggestion can be showed only if the proposed ChargingSocket is currently free and not booked
	all action: ChargingAction | (action.socket.attachedCar = none and (
		no p: Prenotation | p.socket = action.socket and p.validUntil.value > action.validFrom.value))
}

fact suggestionIsCoherentWithUserSchedule {
	// Each suggestion is based on an appointment of the user or on a price reduction
	all sugg: Suggestion | (some schedule: Schedule | schedule in sugg.user.schedules and
		schedule.location = sugg.location and sugg.validFrom.value <= schedule.startingTime.value )
		or
		(one group: ChargingSocketsGroup | sugg.socket in group.sockets and
			group.currentEnergyPrice = DISCOUNT)
}

fact noDuplicatePrenotationForSameUser {
	// A user can't book a socket while he has already booked one
	no disjoint p1, p2: Prenotation | (p1.user = p2.user and (p1.validFrom.value >= p2.validUntil.value or p2.validFrom.value >= p1.validUntil.value))
}

// TODO this assertion could be removed because redundant - behaviour already specified while defining "id" field
fact carMustBeChargingOnASocket {
	all c: Car | c.batteryState = CHARGING implies (
		one s: ChargingSocket | s.attachedCar = c)
}

assert carIsCharging {
	all c: Car | c.batteryState = CHARGING implies (
		c.chargeSecondsLeft > 0 and c.absorbedPower > 0 and one s: ChargingSocket | s.attachedCar = c)
}

check carIsCharging for 6

assert grantPrenotationAndSuggestrionsToNonChargingCars {
	no c: Car | c.batteryState = CHARGING and (some action: ChargingAction | action.user.car = c)
}

check grantPrenotationAndSuggestrionsToNonChargingCars for 5

// TODO remember: every "sub-entity" (e.g. BatteryLevel) can't exist independently (i.e. without a BatteryState). Has this to be formalized? Otherwise
// the world isn't realistic
pred createSuggestionBasedOnSchedule {

}

pred createSuggestionBasedOnDiscount {

}

// With many attributes the model is not so clear, how to fix?
// What to do with Double?
// Why do some simple constraints create problems?

pred world  {
	#User >= 3
	#Schedule >= 4
	#ChargingAction >= 5
	#Timestamp >= 3
	some c: ChargingAction | c = Prenotation
}

run world for 7
