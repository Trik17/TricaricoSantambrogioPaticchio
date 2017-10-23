open util/integer
open util/boolean

sig System{//it's the application and the date is the device's one
	date: one Int,
	users: one User
}

/*sig Date{
	day: Int
}

sig Time{
	hour:Int
}*/

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
	contains: set Appointment,
	date: one Int
}

fact Statechart{
	all s: System, d: DailySchedule | (s.users.calendar.date>s.date)<=> d.status=Coming
	all s: System, d: DailySchedule | (s.users.calendar.date=s.date)<=> d.status=InProgress
	all s: System, d: DailySchedule | (s.users.calendar.date<s.date)<=> d.status=Completed
//	no d1,d2: DailySchedule | d1.date=d2.date
}

sig Appointment {
	predecessor: lone Appointment,
	successor: lone Appointment,  //in un daily schedule ci deve essere esattamente uno senza pred e uno senza succ
//	date: one Int,
	startingTime: one Int,
	finalTime: one Int,
	associatedItinerary: one Itinerary,
//	isContained: one DailySchedule
}
/*{	
	this.startingTime>=0
	this.finalTime>=0
}*/
abstract sig ItineraryStatus{}

one sig Computed extends ItineraryStatus{}
one sig Progressing extends ItineraryStatus{}
one sig Finished extends ItineraryStatus{}

sig Itinerary{
	associatedAppointment: one Appointment,
	startingTime: Int,
	duration: Int,
      itineraryStatus: one ItineraryStatus
}


fact AppointmentConstraints{
	all a: Appointment | a.predecessor != a.successor
	all a: Appointment | a.finalTime >= a.startingTime
	// No overlapping
	all a: Appointment | (#a.predecessor=1) => a.startingTime > a.predecessor.finalTime 
	all a: Appointment | (#a.successor=1) => a.finalTime<a.successor.startingTime
}

fact AllInTheTree{
	all u: User| u in System.users
all u1,u2:User, s1,s2:System | (s1!=s2 && u1 in s1.users && u2 in s2.users)=>(u1!=u2 && u1 not in s2.users && u2 not in s1.users)
	all d: DailySchedule| d in User.calendar
all u1,u2:User, d1,d2:DailySchedule | (u1!=u2 && d1 in u1.calendar && d2 in u2.calendar)=>(d1!=d2 && d1 not in u2.calendar && d2 not in u1.calendar)
	all a:Appointment | a in DailySchedule.contains
all a1,a2: Appointment, d1,d2: DailySchedule | (d1!=d2 && a1 in d1.contains && a2 in d2.contains)=>(a1!=a2 && a1 not in d2.contains && a2 not in d1.contains)
	all i: Itinerary | i in Appointment.associatedItinerary
all i1,i2:Itinerary , a1,a2: Appointment | (a1!=a2 && i1 in a1.associatedItinerary && i2 in a2.associatedItinerary)=>(i1!=i2 && i1 not in a2.associatedItinerary && i2 not in a1.associatedItinerary)
}


/*fact ContainConstraint{
	isContained = ~contains
}*/

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
assert NoThingOutsideTree{
	no u: User| u not in System.users
	no d: DailySchedule| d not in User.calendar
	no a:Appointment | a not in DailySchedule.contains
	no i: Itinerary | i not in Appointment.associatedItinerary
}
pred show{
}
//check NoThingOutsideTree
run show for 10// but exactly 3 User, exactly 1 DailySchedule
check NoOverlappingInDailySchedule 
 
