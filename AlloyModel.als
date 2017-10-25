open util/integer
open util/boolean




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
	startingTimeIt: Int,
	duration: Int,
      itineraryStatus: one ItineraryStatus
}{
startingTimeIt>=0
duration>=0
}




fact AllInTheTree{

// each Itinerary must be in a appointment
	all i: Itinerary | i in Appointment.associatedItinerary
// each Itinerary must belong with one and only one appointment 
all i1,i2:Itinerary , a1,a2: Appointment | (a1!=a2 && i1 in a1.associatedItinerary && i2 in a2.associatedItinerary)=>
(i1!=i2 && i1 not in a2.associatedItinerary && i2 not in a1.associatedItinerary)
}


/*fact ContainConstraint{
	isContained = ~contains
}*/

//manca definizione + dopo il check di come inserire gli itinerary

fact itineraryConstraint{
	associatedItinerary = ~associatedAppointment
}

fact AppointmentAndItineraryAssociated{
	all i: Itinerary| ((add[i.startingTimeIt,i.duration]) < i.associatedAppointment.startingTime) &&
		( i.startingTimeIt >= i.associatedAppointment.predecessor.finalTime) 
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
assert ArriveInTime{
	no  i: Itinerary| ((add[i.startingTimeIt,i.duration]) >= i.associatedAppointment.startingTime) &&
		 i.startingTimeIt < i.associatedAppointment.predecessor.finalTime
}

pred show{
#System=1
#User=1
#DailySchedule=1

}
//check ArriveInTime
//check NoThingOutsideTree
run show for 10
check NoOverlappingInDailySchedule 
 
