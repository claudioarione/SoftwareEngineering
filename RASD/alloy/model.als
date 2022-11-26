// TODO - ask if it's needed to speciffy DSO entity
// TODO until now I have left the Int for power values, assuming that if a user has a fast-charging car he can be shown also suggestions related to
// slow-charging sockets. Can the model be left as it is?

// TODO move secondsLeft in ChargingSocket and away from Car

--------------------------------------------------------------------------SIGNATURES----------------------------------------------------------------------------

sig UserId{}

sig User  {
	id: disj one UserId,
	car: one Car,
	schedules: set Schedule
}

sig Car {
	batteryState: one BatteryState,
	absorbedPower: one Int,
	chargeSecondsLeft: one Int
} {
	chargeSecondsLeft >= 0
	absorbedPower >= 0
}

abstract sig BatteryState {}
lone sig NEEDS_CHARGING extends BatteryState {}
lone sig CHARGING extends BatteryState {}
lone sig CHARGED extends BatteryState {}

sig Schedule {
	startingTime: one Timestamp,
	endingTime: one Timestamp,
	location: one Location
} {
	startingTime.value < endingTime.value
}

sig Timestamp {
	// This value represents the "epoch time", i.e. the number of seconds since 1st January 1970, as done in practice by many systems
	value: one Int
} {
	value > 0
}

sig Location {}

sig CPO {
	stations: set ChargingStation
}

abstract sig EnergyPrice {
	// The declaration of an Int field "price", although natural, is omitted because not relevant for the model
}
sig STANDARD extends EnergyPrice {}
sig DISCOUNT extends EnergyPrice {}

-- How is the logical structure of a ChargingStation organized?
-- Every station contains a set of ChargingSocketsGroup, which, as the name itself says, represent a set of sockets of the same
--  ChargingSocketType (i.e. fast/rapid/slow charging mode). Every group is associated to his current EnergyPrice, which of course does
-- not depend on the specific socket within the group.
-- Finally, every ChargingSocket can have - or not - an attached Car, which of course has to be in charging state
sig ChargingStation {
	location: one Location,
	chargingSocketsGroups: some ChargingSocketsGroup
}

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

abstract sig ChargingSocketType {
	// We assume that the maximum power erogated by each socket type is standardized and doesn't depend on the specific charging station
	maxErogatedPower: one Int
} {
	maxErogatedPower > 0
}
lone sig SLOW extends ChargingSocketType {}
lone sig RAPID extends ChargingSocketType {}
lone sig FAST extends ChargingSocketType {}

abstract sig ChargingAction {
	// We assume that a user can book a specific ChargingSocket
	socket: one ChargingSocket,
	user: one User,
	validFrom: one Timestamp,
	validUntil: one Timestamp
} {
	validFrom.value < validUntil.value
}
sig Suggestion extends ChargingAction {}
sig Prenotation extends ChargingAction {}

---------------------------------------------------------------------------FACTS----------------------------------------------------------------------------

-- Facts related to power

fact erogatedPowerConstraint {
	// The maximum erogated power for fast charge is grater than the one for rapid charge, which is greater than the one for slow charge
	FAST.maxErogatedPower > RAPID.maxErogatedPower and RAPID.maxErogatedPower > SLOW.maxErogatedPower
}

fact onlyChargingCarsAbsorbePower {
	// Only the cars that are actually charging can absorbe power
	all car: Car | (car.absorbedPower = 0) iff not (car.batteryState = CHARGING)
}

fact maxErogatedPowerSufficient {
	// The amount of power absorbed by a car cannot exceed the power erogated by the socket it's connected to
	all group: ChargingSocketsGroup | (all sock: ChargingSocket |
		(sock in group.sockets) implies (sock.attachedCar.absorbedPower <= sock.type.maxErogatedPower)) and
		(some sock: ChargingSocket | (sock in group.sockets) implies (sock.attachedCar.absorbedPower = sock.type.maxErogatedPower))
}


-- Fact related to seconds left until one socket of a certain type is free

fact timeUntilOneGroupSocketIsFreeIsCoherent {
	// If there's a free socket then the attribute secondsUntilFreed = 0, otherwise "secondsUntilFree" is the minimum
	// among all "secondsLeft" attributes of the charging cars
	all group: ChargingSocketsGroup | (group.secondsUntilFree = 0 iff (
		some socket: ChargingSocket | (socket in group.sockets and no c: Car | (c = socket.attachedCar) )))
	and
	all group: ChargingSocketsGroup, socket: ChargingSocket, car: Car |
		(socket in group.sockets and car = socket.attachedCar) implies group.secondsUntilFree <= car.chargeSecondsLeft
}


-- Fact related to coherent existence of entities

fact noChargingGroupWithoutStation {
	// A ChargingSocketsGroup cannot exist if not associated to a ChargingStation
	all g: ChargingSocketsGroup | (one s: ChargingStation | g in s.chargingSocketsGroups)
}

fact noSocketWithoutChargingGroup {
	// A ChargingSocket cannot exist if not associated to a ChargingSocketsGroup
	all sock: ChargingSocket | (one group: ChargingSocketsGroup | sock in group.sockets)
}

fact noCarWithoutUser {
	// A Car cannot exist if not associated to a User
	all c: Car | (one u: User | c = u.car)
}

fact noScheduleWithoutUser {
	// A Schedule cannot exist if not associated to a User
	all s: Schedule | (one u: User | s in u.schedules)
}

fact noBatteryStateWithoutCar {
	// A BatteryState cannot exist if not associated to a Car
	all state: BatteryState | (some c: Car | state = c.batteryState)
}

fact noEnergyPriceWithoutGroup {
	// A EnergyPrice cannot exist if not associated to a ChargingSocketsGroup
	all e: EnergyPrice | (one group: ChargingSocketsGroup | e = group.currentEnergyPrice)
}

fact noChargingStationWithoutCPO {
	// A ChargingStation cannot exist if not associated to a CPO
	all s: ChargingStation | (one cpo: CPO | s  in cpo.stations)
}

// TODO add missing constraints

-- Facts related to ChargingSocketGroups

fact allSocketsInGroupHaveSameType {
	// All the sockets belonging to the same group have the same charging type (fast/rapid/slow)
	all group: ChargingSocketsGroup, socket1, socket2: ChargingSocket |
		(socket1 in group.sockets and socket2 in group.sockets) implies socket1.type = socket2.type
}

fact noTwoGroupsWithSameChargingType {
	// There cannot exists two charging groups belonging to the same station and providing the same charging type
	no disjoint g1, g2: ChargingSocketsGroup | (one station: ChargingStation | g1 in station.chargingSocketsGroups and g2 in station.chargingSocketsGroups) and
 		(some disjoint s1, s2: ChargingSocket | (s1 in g1.sockets and s2 in g2.sockets and s1.type = s2.type) )
}

fact noEmptyGroups {
	// Every charging group can exist only if it contains at least a socket
	all g: ChargingSocketsGroup | (some s: ChargingSocket | s in g.sockets)
}


-- Facts related to Car entities

fact chargingCarHasCorrectType {
	// If a car is being charged, its BatteryState must be CHARGING or CHARGED - it could happen that the recharge
	// is finished but the car is still attached
	all socket: ChargingSocket | (socket.attachedCar != none implies socket.attachedCar.batteryState = CHARGING)
}

fact onlyChargingCarsHaveSecondsLeft {
	// If a car is not charging or is fully charged it does not absorbe power from the socket
	all car: Car | (car.chargeSecondsLeft = 0) iff not (car.batteryState = CHARGING)
}

fact carMustBeChargingOnASocket {
	// If a car is in charging state it must be connected to a socket
	all c: Car | c.batteryState = CHARGING implies (
		one s: ChargingSocket | s.attachedCar = c)
}


-- Facts related to ChargingAction entities - i.e. Prenotation and Suggestion entities

fact chargingActionPresentOnlyIfCarNeedsCharging {
	// Every charging action - a Prenotation or a Suggestion - is related to a car that needs charging
	all a: ChargingAction | a.user.car.batteryState = NEEDS_CHARGING
}

fact chargingActionOnlyIfSocketFree {
	// The Prenotation or the Suggestion can be showed only if the proposed ChargingSocket is currently free
	all a: ChargingAction | (a.socket.attachedCar = none)
}

fact noSuggestionsIfSocketBooked {
	// The Suggestion can be showed only if the proposed ChargingSocket is not already booked
	no s: Suggestion, p: Prenotation | (p.socket = s.socket and (p.validFrom.value <= s.validUntil.value))
}

fact noPrenotationsIfSocketBooked {
	// The Prenotation can be showed only if the proposed ChargingSocket is not already booked
	no disjoint p1, p2: Prenotation | (p1.socket = p2.socket)
}

fact noFurtherPrenotationsForSameUser {
	// A user can't book a socket in a time interval during which he has another active prenotation
	no disjoint p1, p2: Prenotation | (p1.user = p2.user)
}

fact noDuplicateSuggestions {
	no disjoint s1, s2: Suggestion | (s1.socket = s2.socket and s1.user = s2.user and
		(s1.validFrom.value = s2.validFrom.value or s1.validUntil.value = s2.validUntil.value))
}

fact noSuggestionIfUserHasPrenotation {
	no p: Prenotation, s: Suggestion | p.user = s.user
}

fact suggestionIsCoherentWithUserSchedule {
	// Each suggestion is based on an appointment of the user or on a price reduction
	all sugg: Suggestion | ((some schedule: Schedule | schedule in sugg.user.schedules and
		schedule.location = sugg.location and sugg.validFrom.value <= schedule.startingTime.value )
		or
		(one group: ChargingSocketsGroup | sugg.socket in group.sockets and
			group.currentEnergyPrice = DISCOUNT))
}

------------------------------------------------------------------------ASSERTIONS----------------------------------------------------------------------------

assert correctNumberOfChargingGroups {
	// Every station can't have at maximum one group for every charging type
	all s: ChargingStation | #s.chargingSocketsGroups <= #ChargingSocketType
}

//check correctNumberOfChargingGroups for 5

assert carIsCharging {
	// Assert that when a car is in charging state all the related attributes have to be coherent
	all c: Car | c.batteryState = CHARGING iff (
		c.chargeSecondsLeft > 0 and c.absorbedPower > 0 and one s: ChargingSocket | (
			s.attachedCar = c and s.type.maxErogatedPower >= c.absorbedPower))
}

//check carIsCharging for 5

assert grantPrenotationAndSuggestionsToNonChargingCars {
	no c: Car | c.batteryState = CHARGING and (some action: ChargingAction | action.user.car = c)
}

//check grantPrenotationAndSuggestionsToNonChargingCars for 5

assert giveSuggestionsBasedOnPriceOrLocation {
	// There are no suggestions for a non-discount price in a Location where the user doesn't have an appointment in
	no s: Suggestion | (one group: ChargingSocketsGroup | s.socket in group.sockets and group.currentEnergyPrice = STANDARD) and
		(no sch: Schedule | sch in s.user.schedules and sch.location = s.location)
}

//check giveSuggestionsBasedOnPriceOrLocation for 5


-----------------------------------------------------------------------PREDICATES----------------------------------------------------------------------------

-- This generated instance reported in the picture shows a CPO with one station which has two sockets, one with fast charge and the other
-- one with rapid charge. The former is charging Car1, owned by User0. Car0 doesn't need to be attached to a socket because its battery is charged.
-- We can observe that the number of seconds left until the car is charged is equal to the number of seconds until a fast-charging socket is free and
-- that the power absorbed by the car is less than the maximum power available in the socket, as expected
pred usersAndCarsWorld {
	#Car >= 2
	#CPO = 1
	#ChargingSocketsGroup >= 2
	some c: Car | c.batteryState = CHARGING
}

run usersAndCarsWorld for 4

-- The instance is projected over ten sigs, in order to focuse more on the actual interations between the entities
-- Simulation that shows how prenotations and suggestions can combine together
-- As expected, the users which have an active prenotation (i.e. User0 and User1) don't receive suggestions, while
-- User2, which has no prenotations. can receive more than one suggestion.
-- There are a prenotation and a suggestion for each charging socket, but the two don't collide - in particular,
-- the prenotations are from timestamp 3 to timestamp 5, while the suggestions are from 1 to 2, therefore compatible
-- with the desidered modelization of the system
pred prenotationsAndSuggestionsWorld  {
	#User <= 3
	#Suggestion > 1
	#Prenotation > 1
	#ChargingSocket <= 2
	all u: User | (some c: ChargingAction | c.user = u)
}

run prenotationsAndSuggestionsWorld for 4
