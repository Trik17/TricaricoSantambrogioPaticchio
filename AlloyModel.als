

//manca definizione + dopo il check di come inserire gli itinerary
assert NoOverlappingInDailySchedule{
	all d: DailySchedule | no a1, a2: d.contains | 
	a1.startingTime<a2.startingTime and ((a1.finalTime>a2.startingTime)  
	or (a1.finalTime>a2.finalTime)) 
}

assert NoThingOutsideTree{
	no u: User| u not in System.users
	no d: DailySchedule| d not in User.calendar
	no a:Appointment | a not in DailySchedule.contains
	no i: Itinerary | i not in Appointment.associatedItinerary
}

assert ArriveInTime{
	no  i: Itinerary| ((add[i.startingTimeIt,i.duration]) >= i.associatedAppointment.startingTime) &&
		 i.startingTimeIt < i.associatedAppointment.predecessor.finalTime
}
