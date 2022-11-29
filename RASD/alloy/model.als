// TODO - ask if it's needed to specify DSO entity

// TODO move secondsLeft in ChargingSocket and away from Vehicle

--------------------------------------------------------------------------SIGNATURES----------------------------------------------------------------------------

sig UserId{}

sig User  {
	id: disj one UserId,
	vehicle: one Vehicle, // For simplicity, in the Alloy model the User isn't allowed to register more than one vehicle
	schedule: set Appointment
}

sig Vehicle {
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

sig Appointment {
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
-- Finally, every ChargingSocket can have - or not - an attached Vehicle, which of course has to be in charging state
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
	attachedVehicle: lone Vehicle
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
sig Reservation extends ChargingAction {}

---------------------------------------------------------------------------FACTS----------------------------------------------------------------------------

-- Facts related to power

fact erogatedPowerConstraint {
	// The maximum erogated power for fast charge is grater than the one for rapid charge, which is greater than the one for slow charge
	FAST.maxErogatedPower > RAPID.maxErogatedPower and RAPID.maxErogatedPower > SLOW.maxErogatedPower
}

fact onlyChargingVehiclesAbsorbePower {
	// Only the vehicles that are actually charging can absorbe power
	all v: Vehicle | (v.absorbedPower = 0) iff not (v.batteryState = CHARGING)
}

fact maxErogatedPowerSufficient {
	// The amount of power absorbed by a vehicle cannot exceed the power erogated by the socket it's connected to
	all group: ChargingSocketsGroup | (all sock: ChargingSocket |
		(sock in group.sockets) implies (sock.attachedVehicle.absorbedPower <= sock.type.maxErogatedPower)) and
		(some sock: ChargingSocket | (sock in group.sockets) implies (sock.attachedVehicle.absorbedPower = sock.type.maxErogatedPower))
}


-- Fact related to seconds left until one socket of a certain type is free

fact timeUntilOneGroupSocketIsFreeIsCoherent {
	// If there's a free socket then the attribute secondsUntilFreed = 0, otherwise "secondsUntilFree" is the minimum
	// among all "secondsLeft" attributes of the charging vehicles
	all group: ChargingSocketsGroup | (group.secondsUntilFree = 0 iff (
		some socket: ChargingSocket | (socket in group.sockets and no v: Vehicle | (v = socket.attachedVehicle) )))
	and
	all group: ChargingSocketsGroup, socket: ChargingSocket, v: Vehicle |
		(socket in group.sockets and v = socket.attachedVehicle) implies group.secondsUntilFree <= v.chargeSecondsLeft
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

fact noVehicleWithoutUser {
	// A Vehicle cannot exist if not associated to a User
	all v: Vehicle | (one u: User | v = u.vehicle)
}

fact noAppointmentWithoutUser {
	// An Appointment cannot exist if not associated to a User
	all a: Appointment | (one u: User | a in u.schedule)
}

fact noBatteryStateWithoutVehicle {
	// A BatteryState cannot exist if not associated to a Vehicle
	all state: BatteryState | (some v: Vehicle | state = v.batteryState)
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


-- Facts related to Vehicle entities

fact chargingVehicleHasCorrectType {
	// If a vehicle is being charged, its BatteryState must be CHARGING or CHARGED - it could happen that the recharge
	// is finished but the vehicle is still attached
	all socket: ChargingSocket | (socket.attachedVehicle != none implies socket.attachedVehicle.batteryState = CHARGING)
}

fact onlyChargingVehiclesHaveSecondsLeft {
	// If a vehicle is not charging or is fully charged it does not absorbe power from the socket
	all v: Vehicle | (v.chargeSecondsLeft = 0) iff not (v.batteryState = CHARGING)
}

fact vehicleMustBeChargingOnASocket {
	// If a vehicle is in charging state it must be connected to a socket
	all v: Vehicle | v.batteryState = CHARGING implies (
		one s: ChargingSocket | s.attachedVehicle = v)
}


-- Facts related to ChargingAction entities - i.e. Reservation and Suggestion entities

fact chargingActionPresentOnlyIfVehicleNeedsCharging {
	// Every charging action - a Reservation or a Suggestion - is related to a vehicle that needs charging
	all a: ChargingAction | a.user.vehicle.batteryState = NEEDS_CHARGING
}

fact chargingActionOnlyIfSocketFree {
	// The Reservation or the Suggestion can be showed only if the proposed ChargingSocket is currently free
	all a: ChargingAction | (a.socket.attachedVehicle = none)
}

fact noSuggestionsIfSocketBooked {
	// The Suggestion can be showed only if the proposed ChargingSocket is not already booked
	no s: Suggestion, r: Reservation | (r.socket = s.socket and (r.validFrom.value <= s.validUntil.value))
}

fact noReservationsIfSocketBooked {
	// The Reservation can be showed only if the proposed ChargingSocket is not already booked
	no disjoint r1, r2: Reservation | (r1.socket = r2.socket)
}

fact noFurtherReservationsForSameUser {
	// A user can't book a socket in a time interval during which he has another active reservations
	no disjoint r1, r2: Reservation | (r1.user = r2.user)
}

fact noDuplicateSuggestions {
	// There can't be two suggestions for the same user and socket in a colliding time interval
	no disjoint s1, s2: Suggestion | (s1.socket = s2.socket and s1.user = s2.user and
		(s1.validFrom.value = s2.validFrom.value or s1.validUntil.value = s2.validUntil.value))
}

fact noSuggestionIfUserHasReservation {
	// No suggestions are showed to users which already have a reservations
	no r: Reservation, s: Suggestion | r.user = s.user
}

fact suggestionIsCoherentWithUserAppointment {
	// Each suggestion is based on an appointment of the user or on a price reduction
	all sugg: Suggestion | (some a: Appointment | a in sugg.user.schedule and sugg.validFrom.value <= a.startingTime.value and
		(one station: ChargingStation, group: ChargingSocketsGroup | group in station.chargingSocketsGroups and sugg.socket in group.sockets and
		station.location = a.location) )
		or
		(one group: ChargingSocketsGroup | sugg.socket in group.sockets and
			group.currentEnergyPrice = DISCOUNT)
}

------------------------------------------------------------------------ASSERTIONS----------------------------------------------------------------------------

assert correctNumberOfChargingGroups {
	// Every station can't have at maximum one group for every charging type
	all s: ChargingStation | #s.chargingSocketsGroups <= #ChargingSocketType
}

check correctNumberOfChargingGroups for 5

assert vehicleIsCharging {
	// Assert that when a vehicle is in charging state all the related attributes have to be coherent
	all v: Vehicle | v.batteryState = CHARGING iff (
		v.chargeSecondsLeft > 0 and v.absorbedPower > 0 and one s: ChargingSocket | (
			s.attachedVehicle = v and s.type.maxErogatedPower >= v.absorbedPower))
}

check vehicleIsCharging for 5

assert grantReservationAndSuggestionsToNonChargingVehicles {
	no v: Vehicle | v.batteryState = CHARGING and (some action: ChargingAction | action.user.vehicle = v)
}

check grantReservationAndSuggestionsToNonChargingVehicles for 5

assert giveSuggestionsBasedOnPriceOrLocation {
	// There are no suggestions for a non-discount price in a Location where the user doesn't have an appointment in
	no s: Suggestion | (one group: ChargingSocketsGroup | s.socket in group.sockets and group.currentEnergyPrice = STANDARD and
		(no a: Appointment | a in s.user.schedule and (
			one station: ChargingStation |  group in station.chargingSocketsGroups and station.location = a.location)))
}

check giveSuggestionsBasedOnPriceOrLocation for 5


-----------------------------------------------------------------------PREDICATES----------------------------------------------------------------------------

-- This generated instance reported in the picture shows a CPO with one station which has two sockets, one with fast charge and the other
-- one with rapid charge. The former is charging Vehicle1, owned by User0. Vehicle0 doesn't need to be attached to a socket because its battery is charged.
-- We can observe that the number of seconds left until the vehicle is charged is equal to the number of seconds until a fast-charging socket is free and
-- that the power absorbed by the vehicle is less than the maximum power available in the socket, as expected
pred usersAndVehiclesWorld {
	#Vehicle >= 2
	#CPO = 1
	#ChargingSocketsGroup >= 2
	some v: Vehicle | v.batteryState = CHARGING
}

run usersAndVehiclesWorld for 4

-- The instance reported in the picture hides many relations in order to focus only on the aspects described below
-- All the three suggestions are for the same user. Suggestion2 is based on the entity Appointment associated to the user: in fact,
-- the proposed socket (ChargingSocket0) belongs to a station which is in the same location as the one the user saved in his/her
-- schedule and both the schedule and the suggestion are in the time interval 1-4.
-- Suggestion0 and Suggestion1 are two suggestions on the same socket (ChargingSocket1) but regarding different time intervals. They are
-- valid suggestions because the charging group the two sockets belong to offers a discount on the energy price
pred suggestionsWorld {
	#Suggestion = 3
	#Appointment = 1
	#User = 1
	#ChargingSocket < #Suggestion
	#Reservation = 0
	one c: ChargingSocketsGroup | c.currentEnergyPrice = DISCOUNT
	one s: Suggestion | (one c: ChargingSocketsGroup | c.currentEnergyPrice = STANDARD and s.socket in c.sockets )
}

run suggestionsWorld for 4

-- The instance is projected over ten sigs, in order to focuse more on the actual interations between the entities
-- Simulation that shows how reservations and suggestions can combine together
-- As expected, the users which have an active reservation (i.e. User0 and User1) don't receive suggestions, while
-- User2, which has no reservations. can receive more than one suggestion.
-- There are a reservation and a suggestion for each charging socket, but the two don't collide - in particular,
-- the reservations are from timestamp 3 to timestamp 5, while the suggestions are from 1 to 2, therefore compatible
-- with the desired modelization of the system
pred reservationsAndSuggestionsWorld  {
	#User <= 3
	#Suggestion > 1
	#Reservation > 1
	#ChargingSocket <= 2
	all u: User | (some c: ChargingAction | c.user = u)
}

run reservationsAndSuggestionsWorld for 4