open util/integer
open util/time
open util/boolean

sig User {
	username: one String,
	dailySchedules: set DailySchedule
}

enum DailyScheduleStatus{Coming, InProgress, Completed}

sig DailySchedule{
	status: one DailyScheduleStatus,
	date: one Int,
	contains: some Appointment
}

sig Appointment {
	date: one Int,
	time: one Time, 
	isContained: one DailySchedule
}

fact ContainConstraint{
	isContained = ~contains
}

pred show{}

run show for 5 
