open util/integer
open util/boolean

sig System{//it's the application and the date is the device's one
	time: one Time,
	users: one User
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

sig Appointment {
	predecessor: lone Appointment,
	successor: lone Appointment,  //in un daily schedule ci deve essere esattamente uno senza pred e uno senza succ
	startingTime: one Time,
	finalTime: one Time,
// 	associatedItinerary: one Itinerary,
//	isContained: one DailySchedule
}{
startingTime.date=finalTime.date
startingTime.hour<finalTime.hour
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

fact DailyScheduleStateChart{
	all s: System, d: s.users.calendar | (d.date>s.time.date) <=> d.status=Coming
	all s: System, d: s.users.calendar  | (d.date=s.time.date) <=> d.status=InProgress
	all s: System, d: s.users.calendar  | (d.date<s.time.date) <=> d.status=Completed
}
fact noUselessTime{
	all t: Time| (t in System.time) or (t in Appointment.startingTime) or (t in Appointment.finalTime) //poiITINERARY
}

fact AppointmentDailyScheduleTree{
	// each appointment must be in a dailyschedule
	all a:Appointment | a in DailySchedule.contains
	//each appointment must be in one and only one dailyschedule
	all a1,a2: Appointment, d1,d2: DailySchedule | (d1!=d2 && a1 in d1.contains && a2 in d2.contains)=>
	(a1!=a2 && a1 not in d2.contains && a2 not in d1.contains)
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

assert noOverlappingAppointments{
//if two appointment overlap, they belongs with different users
	all a1,a2: Appointment, u1,u2: User | (a1.startingTime.date=a2.startingTime.date && a1!=a2 &&  (a1 in u1.calendar.contains && a2 in u2.calendar.contains) 
										&& (a1.startingTime.hour>=a2.startingTime.hour && a1.startingTime.hour=<a2.finalTime.hour)) 
										=> (u1!=u2)
}

assert samePredecessorSuccessorDate{
	all a1, a2: Appointment | (a2 in a1.predecessor) => (a1.startingTime.date=a2.startingTime.date)
	all a1, a2: Appointment | (a2 in a1.successor) => (a1.startingTime.date=a2.startingTime.date)
 }



pred show{}

check noOverlappingAppointments
//check samePredecessorSuccessorDate
//check AppointmentOrdering
//check OnlyOneDSInProgress
run show for 15 but exactly 1 System, exactly 1 User, exactly 4 DailySchedule
