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
	aDuration: one Int,
// 	associatedItinerary: one Itinerary,
//	isContained: one DailySchedule
}{
aDuration>0
}

fact AppointmentConstraints{
	predecessor=~successor
	all a: Appointment | a.predecessor!=a
	all a: Appointment | a.successor!=a
	//If there is a predecessor, then it must end before its successor
	all a1, a2: Appointment | (a2 in a1.predecessor) => (a1.startingTime.hour>addition[a2.startingTime.hour,a2.aDuration] )
	//If there is a successor, then it must start after its predecessor
	all a1,a2 : Appointment | (a2 in a1.successor) => (addition[a1.startingTime.hour,a1.aDuration]<a2.startingTime.hour) 
	//There is only one appointment in a daily schedule without a predecessor/successor
//	all d: DailySchedule | (#d.contains = (add[#d.contains.predecessor,1] ))&& ( #d.contains =( add[#d.contains.successor,1]))
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

fun addition (n1: Int, n2:Int): Int{
	{answer: Int| answer= n1+n2}
}


//There is only One DailyScheduleInProgress
assert OnlyOneDSInProgress{
	all u:User, d1,d2: DailySchedule | (d1.status=InProgress && d1 in u.calendar && d2 in u.calendar && d1!=d2) => (d2.status!=InProgress)
}

assert AppointmentOrdering1{
//	all a: Appointment |((#a.successor=1) && (#a.predecessor=1) )=> a.predecessor != a.successor
	no a: Appointment, n: addition[a.startingTime.hour,a.aDuration]| a.startingTime.hour >n
}

assert AppointmentOrdering2{
	all a1,  a2: Appointment| (a2 in a1.predecessor) => a1!=a2
//	all a1,  a2: Appointment| (a2 in a1.successor) => a1!=a2
}

assert a{
	no n,a,b: Time| n.date=addition[a.date,b.date]
}

pred show{

}
check a
//check AppointmentOrdering2
//check OnlyOneDSInProgress
run show for 5 but 1 DailySchedule
