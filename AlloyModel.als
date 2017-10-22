open util/integer
open util/boolean

sig System{
	date: one Date,
	users: one User
}

sig Date{
	day: Int
}

sig Time{
	hour:Int
}

sig User {
//	username: Name,
//	id: Int,
	calendar: set DailySchedule
}

abstract sig DailyScheduleStatus{}

one sig Coming extends DailyScheduleStatus{}
one sig InProgress extends DailyScheduleStatus{}
one sig Completed extends DailyScheduleStatus{}

sig DailySchedule{
	status: one DailyScheduleStatus,
	contains: some Appointment
}

sig Appointment {
	predecessor: lone Appointment,
	successor: lone Appointment,
	date: one Date,
	startingTime: one Time,
	finalTime: one Time,
	associatedItinerary: one Itinerary
}


fact AppointmentConstraints{
	all a: Appointment | a.predecessor != a.successor
	all a: Appointment | a.finalTime.hour >= a.startingTime.hour
	// No overlapping
	all a: Appointment | (#a.predecessor=1) => a.startingTime.hour > a.predecessor.finalTime.hour 
	all a: Appointment | (#a.successor=1) => a.finalTime.hour<a.successor.startingTime.hour
}



abstract sig ItineraryStatus{}

one sig Computed extends ItineraryStatus{}
one sig Progressing extends ItineraryStatus{}
one sig Finished extends ItineraryStatus{}

fact tree{
	all u: User, s:System | u in s.users
	all d: DailySchedule| d in User.calendar
	all a:Appointment | a in DailySchedule.contains
	all i: Itinerary | i in Appointment.associatedItinerary
}
sig Itinerary{
	associatedAppointment: one Appointment,
	startingTime: Time,
	duration: Int,
      itineraryStatus: one ItineraryStatus
}

//fact ContainConstraint{
//	isContained = ~contains
//}

//manca definizione + dopo il check di come inserire gli itinerary

fact itineraryConstraint{
	associatedItinerary = ~associatedAppointment
	all i: Itinerary, a: i.associatedAppointment | ((i.startingTime.hour+i.duration) <= a.startingTime.hour) &&
		 i.startingTime.hour >= a.predecessor.finalTime.hour
}

fact ItineraryDurationConstraint{
	no a: Appointment | a.associatedItinerary.duration <= a.startingTime.hour - a.predecessor.finalTime.hour
}
//per sottrarre c'è la sub

assert NoOverlappingInDailySchedule{
	all d: DailySchedule | no a1, a2: d.contains | 
	a1.startingTime.hour<a2.startingTime.hour and ((a1.finalTime.hour>a2.startingTime.hour)  
	or (a1.finalTime.hour>a2.finalTime.hour)) 
}
assert NoThingOutsideTree{
	no u: User, s:System | u not in s.users
	no d: DailySchedule| d not in User.calendar
	no a:Appointment | a not in DailySchedule.contains
	no i: Itinerary | i not in Appointment.associatedItinerary
}
pred show{
}
//check NoThingOutsideTree
run show for 5 but exactly 1 System, exactly 1 User, exactly 1 DailySchedule
check NoOverlappingInDailySchedule 
 
