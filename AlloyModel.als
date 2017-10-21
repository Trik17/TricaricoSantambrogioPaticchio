open util/integer
open util/boolean

sig System{
	date: one Int
}

sig User {
	username: one String,
	dailySchedules: set DailySchedule
}

enum DailyScheduleStatus{Coming, InProgress, Completed}

sig DailySchedule{
	status: one DailyScheduleStatus,

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
	//date = isContained.date
	finalTime > startingTime
}

fact f{
all a: Appointment | a.startingTime > a.predecessor.finalTime && a.finalTime<a.successor.startingTime
all a: Appointment | a.date = a.isContained.date
}

enum ItineraryStatus{Computed, Progressing, Finished}

sig Itinerary{
	associatedAppointment: one Appointment,
	startingTime: one Int,
	finalTime: one Int,
	itineraryStatus: one ItineraryStatus
}

fact ContainConstraint{
	isContained = ~contains
}

fact itineraryConstraint{
	associatedItinerary = ~associatedAppointment
	all i: Itinerary, a: i.associatedAppointment | i.startingTime < a.startingTime && i.startingTime >= a.predecessor.finalTime
}

pred show{}

run show for 5 
