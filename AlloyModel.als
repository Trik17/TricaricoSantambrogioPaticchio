open util/integer
open util/boolean

sig System{
	date: one Int,
	users: one User
}

sig User {
	username: one String,
	dailySchedules: set DailySchedule
}

//enum DailyScheduleStatus{Coming, InProgress, Completed}

sig DailySchedule{
	//status: one DailyScheduleStatus,
	contains: some Appointment
}

sig Appointment {
	predecessor: lone Appointment,
	successor: lone Appointment,
	date: one Int,
	startingTime: one Int,
	finalTime: one Int,
	isContained: one DailySchedule,
	associatedItinerary: one Itinerary
}
{
	predecessor != successor
	finalTime > startingTime
}

fact f{
all a: Appointment | a.startingTime > a.predecessor.finalTime && a.finalTime<a.successor.startingTime
all a: Appointment | a.date = a.isContained.date
}

//enum ItineraryStatus{Computed, Progressing, Finished}

sig Itinerary{
	associatedAppointment: one Appointment,
	startingTime: Int,
	duration: Int,
//	itineraryStatus: one ItineraryStatus
}

fact ContainConstraint{
	isContained = ~contains
}
//manca definizione + dopo il check di come inserire gli itinerary

fact itineraryConstraint{
	associatedItinerary = ~associatedAppointment
	all i: Itinerary, a: i.associatedAppointment | ((i.startingTime+i.duration) <= a.startingTime) &&
		 i.startingTime >= a.predecessor.finalTime
}

fact ItineraryDurationConstraint{
	no a: Appointment | a.associatedItinerary.duration <= a.startingTime - a.predecessor.finalTime
}
//per sottrarre c'è la sub

assert NoOverlappingInDailySchedule{
	all d: DailySchedule | no a1, a2: d.contains | 
	a1.startingTime<a2.startingTime and ((a1.finalTime>a2.startingTime)  
	or (a1.finalTime>a2.finalTime)) 
}

pred show{
}

check NoOverlappingInDailySchedule for 5
