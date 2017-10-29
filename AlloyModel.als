open util/integer
//open util/integer as integer
open util/boolean

one sig System{//it's the application and the date is the device's one
	time: one Time,
	users: some User
}

sig Time{ //bisogna inserire che il Time appartiene a system/daily schedule ecc.
date: Int,
hour: Int}
{date>0
hour>=0}

sig User {
	calendar: set DailySchedule
}

abstract sig DailyScheduleStatus{}

one sig Coming extends DailyScheduleStatus{}
one sig InProgress extends DailyScheduleStatus{}
one sig Completed extends DailyScheduleStatus{}

sig DailySchedule{
	status: one DailyScheduleStatus,
	date: one Int,
	contains: some Appointment
}{
date>0
}

abstract sig AppointmentStatus{}
one sig Drafted extends AppointmentStatus{}
one sig Scheduled extends AppointmentStatus{}
one sig Current extends AppointmentStatus{}
one sig Terminated extends AppointmentStatus{}

sig Appointment {
	predecessor: lone Appointment,
	successor: lone Appointment,  
	startingTime: one Time,
	finalTime: one Time,
 	associatedItinerary: one Itinerary,
	appointmentStatus: one AppointmentStatus
//	isContained: one DailySchedule
}{
startingTime.date=finalTime.date
startingTime.hour<finalTime.hour
}

abstract sig ItineraryStatus{}
one sig Computed extends ItineraryStatus{}
one sig Progressing extends ItineraryStatus{}
one sig Finished extends ItineraryStatus{}

sig Itinerary{
	associatedAppointment: one Appointment,
	startingTimeIt: one Time,
	finalTimeIt: one Time,
      itineraryStatus: one ItineraryStatus
}{

}

fact AppointmentConstraints{	
	predecessor=~successor
	all a: Appointment | a.predecessor!=a
	all a: Appointment | a.successor!=a
	//each appointment in a dailyshedule must have the same date of it
	all d: DailySchedule, a: d.contains | d.date=a.startingTime.date
	//If there is a predecessor, then it must end before its successor
	all a1, a2: Appointment | (a2 in a1.predecessor) => (a1.startingTime.hour>a2.finalTime.hour)
	all d: DailySchedule,  a1, a2: Appointment | (a2 in a1.predecessor) => (a1 in d.contains && a2 in d.contains) 
	all d: DailySchedule,  a1, a2: Appointment | (a2 in a1.successor) => (a1 in d.contains && a2 in d.contains) 
	//If there is a successor, then it must start after its predecessor
	all a1,a2 : Appointment | (a2 in a1.successor) => (a2.startingTime.hour>a1.finalTime.hour) 
	//There is only one appointment in a daily schedule without a predecessor/successor
	all d: DailySchedule | (#d.contains = (add[#d.contains.predecessor,1] ))&& ( #d.contains =( add[#d.contains.successor,1]))
}

fact AppointmentAndItineraryAssociated{
	associatedItinerary = ~associatedAppointment
	//each Itinerary of an Appointment must have the same date of it
	all a: Appointment, i: a.associatedItinerary | a.startingTime.date=i.startingTimeIt.date
	//each itinerary is between two consecutive appointments
	all i: Itinerary| i.finalTimeIt.hour =< i.associatedAppointment.startingTime.hour &&
				( i.startingTimeIt.hour >= i.associatedAppointment.predecessor.finalTime.hour) 
}

fact UserSystemTree{
// each user must be in a system
	all u: User| u in System.users
// each user must belong with one and only one system 
all u1,u2:User, s1,s2:System | (s1!=s2 && u1 in s1.users && u2 in s2.users)=>
(u1!=u2 && u1 not in s2.users && u2 not in s1.users)
}

fact DailyScheduleUserTree{
// each DailySchedule must be in a user's calendar
	all d: DailySchedule| d in User.calendar
// each DailySchedule must belong with one and only one user's calendar
	all u1,u2:User, d1,d2:DailySchedule | (u1!=u2 && d1 in u1.calendar && d2 in u2.calendar)=>
(d1!=d2 && d1 not in u2.calendar && d2 not in u1.calendar)
// each user must have at most one daily schedule per date
	all u : User, d1,d2: DailySchedule | (d1!=d2 && d1 in u.calendar && d2 in u.calendar) => (d1.date != d2.date)
}

fact ItineraryAppointmentTree{
all i:Itinerary | i.startingTimeIt.date=i.finalTimeIt.date
all i:Itinerary | i.startingTimeIt.hour<i.finalTimeIt.hour
// each Itinerary must be in a appointment
	all i: Itinerary | i in Appointment.associatedItinerary
// each Itinerary must belong with one and only one appointment 
all i1,i2:Itinerary , a1,a2: Appointment | (a1!=a2 && i1 in a1.associatedItinerary && i2 in a2.associatedItinerary)=>
(i1!=i2 && i1 not in a2.associatedItinerary && i2 not in a1.associatedItinerary)
}

fact AppointmentDailyScheduleTree{






//AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA 		all a: Appointment | #(u.calendar.contains.appointmentStatus -> Drafted)=<1 
						


	// each appointment must be in a dailyschedule except for, at most, one Drafted Appointment (for each User)
	(#(Appointment.appointmentStatus -> Drafted))=<(#User)
	all a:Appointment | ((a.appointmentStatus = Scheduled) or (a.appointmentStatus = Current) or (a.appointmentStatus = Terminated)) 
					=> (a in DailySchedule.contains)
	//each appointment must be in one and only one dailyschedule
	all a1,a2: Appointment, d1,d2: DailySchedule | (d1!=d2 && a1 in d1.contains && a2 in d2.contains)=>
	(a1!=a2 && a1 not in d2.contains && a2 not in d1.contains)
}

fact AppointmentStateChart{
	all s: System, a: s.users.calendar.contains | ((a.startingTime.date=s.time.date) && (a.associatedItinerary.startingTimeIt.hour =< s.time.hour) 
				&&  (a.finalTime.hour >= s.time.hour)) <=> a.appointmentStatus=Current
	all s: System, a: s.users.calendar.contains | ((a.startingTime.date>s.time.date) or ((a.associatedItinerary.startingTimeIt.hour >= s.time.hour) 
				&&  (a.startingTime.date=s.time.date)) )<=> a.appointmentStatus=Scheduled
	all s: System, a: s.users.calendar.contains | ((a.startingTime.date<s.time.date) or ((a.finalTime.hour =< s.time.hour) 
				&&  (a.startingTime.date=s.time.date)) )<=> a.appointmentStatus=Terminated
}

fact DailyScheduleStateChart{
	all s: System, d: s.users.calendar | (d.date>s.time.date) <=> d.status=Coming
	all s: System, d: s.users.calendar  | (d.date=s.time.date) <=> d.status=InProgress
	all s: System, d: s.users.calendar  | (d.date<s.time.date) <=> d.status=Completed
}

fact ItineraryStateChart{
	all s: System, i: s.users.calendar.contains.associatedItinerary | ((i.startingTimeIt.date=s.time.date) && (i.startingTimeIt.hour =< s.time.hour) 
				&&  (i.finalTimeIt.hour >= s.time.hour)) <=> i.itineraryStatus=Progressing
	all s: System, i: s.users.calendar.contains.associatedItinerary | (i.startingTimeIt.date>s.time.date or
				 (i.startingTimeIt.date=s.time.date  and i.startingTimeIt.hour > s.time.hour))<=> i.itineraryStatus=Computed
	all s: System, i: s.users.calendar.contains.associatedItinerary | (i.startingTimeIt.date<s.time.date or
				 (i.startingTimeIt.date=s.time.date  and i.finalTimeIt.hour < s.time.hour))<=> i.itineraryStatus=Finished
}

fact noUselessTime{
	all t: Time| (t in System.time) or (t in Appointment.startingTime) or (t in Appointment.finalTime) //poiITINERARY
}


//There is only One DailyScheduleInProgress
assert OnlyOneDSInProgress{
	all u:User, d1,d2: DailySchedule | (d1.status=InProgress && d1 in u.calendar && d2 in u.calendar && d1!=d2) 
														=>(d2.status!=InProgress)
}

assert AppointmentOrdering{
	all a1,  a2: Appointment | (a2 in a1.predecessor) => a1!=a2
	all a1,  a2: Appointment | (a2 in a1.successor) => a1!=a2
}

assert NoOverlappingAppointments{
//if two appointment overlap, they belong with different users
	all a1,a2: Appointment, u1,u2: User | (a1.startingTime.date=a2.startingTime.date && a1!=a2 &&  (a1 in u1.calendar.contains && a2 in u2.calendar.contains) 
										&& (a1.startingTime.hour>=a2.startingTime.hour && a1.startingTime.hour=<a2.finalTime.hour)) 
										=> (u1!=u2)
}

assert SamePredecessorSuccessorDate{
	//predecessor & successor have the same date
	all a1, a2: Appointment | (a2 in a1.predecessor) => (a1.startingTime.date=a2.startingTime.date)
	all a1, a2: Appointment | (a2 in a1.successor) => (a1.startingTime.date=a2.startingTime.date)
 }

assert OneFirstAndOneLastAppointment{
	all a1,a2: Appointment, d: DailySchedule | (a1.predecessor = none && a2.predecessor = none && a1!=a2 && (a1 in d.contains))=> 
									 		(a2 not in d.contains)
}

assert noOverlappingItineraries{
//if two itineraries overlap, they belong with different users
	all i1,i2: Itinerary, u1,u2: User | (i1!=i2 && i1.itineraryStatus=Progressing && i2.itineraryStatus=Progressing 
										&& i1 in u1.calendar.contains.associatedItinerary && i2 in u2.calendar.contains.associatedItinerary) =>
										(u1!=u2)
}

assert ScheduleItineraryRelationFinished{
//Verify the time when itineraries are finished
	all s: System, d: s.users.calendar , i: d.contains.associatedItinerary | ((d.status=Completed) or (d.status=InProgress && i.finalTimeIt.hour<s.time.hour)) => i.itineraryStatus=Finished
}


assert ScheduleItineraryRelationProgressing{
//Verify that if the itinerary is progressing, then the daily schedule is in progress
	all d: DailySchedule, i: d.contains.associatedItinerary | i.itineraryStatus=Progressing => d.status=InProgress
}

pred timeConsistency[s: System, a: Appointment]{
	s.time.date>=a.startingTime.date
	//(s.time.date=a.startingTime.date)=> (s.time.hour<a.startingTime.hour)
	(s.time.date=a.startingTime.date)=> (s.time.hour<a.associatedItinerary.startingTimeIt.hour)
}


pred newAppointment[s: System, u,u': s.users, a:Appointment]{
	not timeConsistency[s,a] and
	a.appointmentStatus=Drafted and
	a not in u.calendar.contains 
}

pred addAppointment[s: System, u,u': s.users, a:Appointment]{
//	a.appointmentStatus=
	u'.calendar.contains=u.calendar.contains+a	
}

pred showNewAppointment[s: System, u,u': User,a:Appointment]{
	newAppointment[s,u,u',a]
	addAppointment[s,u,u',a]
}


fact show{
	lone a:Appointment | a.appointmentStatus=Drafted
}

pred show{
	
//#System=1
//#s.users=1
//#(s.users.calendar)>1
//#(s.users.calendar.contains)>1
}

/*
check ScheduleItineraryRelationProgressing for 5
check ScheduleItineraryRelationFinished
check noOverlappingItineraries
check OneFirstAndOneLastAppointment
check NoOverlappingAppointments
check SamePredecessorSuccessorDate
check AppointmentOrdering
check OnlyOneDSInProgress
*/

run show for 5 but 1 User, 4 DailySchedule, 4 Appointment
run showNewAppointment for 5  //but 1 User
