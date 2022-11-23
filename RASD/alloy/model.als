// TODO - update Int into Double and ask if it's needed to speciffy DSO entity, replacing
// "currentEnergyPrice" attribute with a more complex structure

abstract sig ChargingSocketType {
	secondsUntilFreed: one Int
}
one sig SLOW extends ChargingSocketType {}
one sig RAPID extends ChargingSocketType {}
one sig FAST extends ChargingSocketType {}

sig User  {
	id: disj one Int,
	name: one String,
	surname: one String,
	car: one Car,
	schedules: set Schedule
}  {
	//  The id of every user is an 8-digit univoque number
	id > 10000000
	id < 100000000
}

// Car - related signatures
sig Car {
	name: one String,
	batteryState: one BatteryState
}

sig BatteryState {
	level: one ChargeLevel,
	capacity: one ChargeLevel,
	powerAbsorbed: one Int
} {
	level.kWh < capacity.kWh
	powerAbsorbed > 0
}

sig ChargeLevel {
	kWh: one Int  // Represents the charge level expressed in kWh
} {
	kWh > 0
}

// Defines an appointment, composed of dates and location
sig Schedule {
	startingTime: one Timestamp,
	endingTime: one Timestamp,
	location: one Location
}

sig Timestamp {
	// This value represents the "epoch time", 
	// i.e. the number of seconds since 1st January 1970, as done in practice by many systems
	value: one Int
} {
	value > 1600000000
}

sig Location {
	latitude: one Int,
	longitude: one Int
} {
	latitude > -90
	latitude < 90
	longitude > -180
	longitude < 180
}

// CPO view 
sig CPO {
	stations: set ChargingStation,
	currentEnergyPrice: one EnergyPrice  // Expressed in €
}

sig EnergyPrice {
	basePrice: one Int,
	discount: one Int
} {
	basePrice > 0
	discount >= 0
	discount < basePrice
}

sig ChargingStation {
	chargingSockets: some ChargingSocket
}

sig ChargingSocket {
	type: one ChargingSocketType,
	costPerKWh: one Int,
	attachedCar: lone ChargingCar
}

sig ChargingCar extends Car {
	// FIXME does powerAbsorbed have to go here or it can be left in Car?
	secondsLeft: one Int
} {
	secondsLeft > 0
}
