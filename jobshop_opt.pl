/* Georgios Tsiris, 1115201700173 */

:- set_flag(print_depth,1000).

:- lib(ic).
:- lib(branch_and_bound).

jobshop_opt(Jobs, Staff, Schedule, Cost, Delta, Timeout) :-
	def_vars(Jobs, StartTimes, FinishTimes, MachinesUsed),
	state_constrs(Jobs, Staff, StartTimes, FinishTimes, MachinesUsed),
	Cost #= max(FinishTimes),
	append(StartTimes, MachinesUsed, Variables),
	bb_min(search(Variables, 0, input_order, indomain, complete, []), Cost, bb_options{delta:Delta, timeout:Timeout}),
	schedule(Jobs, StartTimes, FinishTimes, MachinesUsed, Schedule).

def_vars(Jobs, StartTimes, FinishTimes, MachinesUsed) :-
	get_all_tasks(Jobs, AllTasks),
	length(AllTasks, TaskCount),
	length(StartTimes, TaskCount),
	length(FinishTimes, TaskCount),
	length(MachinesUsed, TaskCount),
	add_durations(AllTasks, WorstCaseDeadline),
	StartTimes #:: 0..WorstCaseDeadline,
	FinishTimes #:: 0..WorstCaseDeadline,
	get_machine_count(MachineCount),
	MachinesUsed #:: 1..MachineCount.

get_all_tasks([], []).
get_all_tasks([Job|Jobs], AllTasks) :-
	get_all_tasks(Jobs, TasksAcc),
	job(Job, Tasks),
	append(Tasks, TasksAcc, AllTasks).

add_durations([], 0).
add_durations([Task|Tasks], TotalDuration) :-
	add_durations(Tasks, DurationAcc),
	task(Task, _, Duration, _),
	TotalDuration is DurationAcc + Duration.

get_machine_count(MachineCount) :-
	get_all_machine_indexes(AllMachineIndexes),
	length(AllMachineIndexes, MachineCount).

get_all_machine_indexes(AllMachineIndexes) :-
	get_all_machines(AllMachines),
	findall(Index, n_th(Index, AllMachines, _), AllMachineIndexes).

get_all_machines(AllMachines) :-
	setof(MachineType, machine(MachineType, _), AllMachineTypes),
	get_machines_of_these_types(AllMachineTypes, AllMachines).

get_machines_of_these_types([], []).
get_machines_of_these_types([MachineType|MachineTypes], Machines) :-
	machine(MachineType, NumberOfMachines),
	length(MachinesOfCurrentType, NumberOfMachines),
	fill_list_with_element(MachineType, MachinesOfCurrentType),
	get_machines_of_these_types(MachineTypes, MachinesAcc),
	append(MachinesOfCurrentType, MachinesAcc, Machines).

fill_list_with_element(_, []).
fill_list_with_element(Element, [Element|Elements]) :-
	fill_list_with_element(Element, Elements).

state_constrs(Jobs, Staff, StartTimes, FinishTimes, MachinesUsed) :-
	get_all_tasks(Jobs, AllTasks),
	duration_constr(AllTasks, StartTimes, FinishTimes),
	tasks_per_job(Jobs, TasksPerJob),
	job_constr(TasksPerJob, StartTimes, FinishTimes),
	machine_constr(AllTasks, MachinesUsed),
	non_conflict_constr(AllTasks, StartTimes, FinishTimes, MachinesUsed),
	add_durations(AllTasks, WorstCaseDeadline),
	staff_constr(AllTasks, StartTimes, FinishTimes, WorstCaseDeadline, Staff).

duration_constr([], [], []).
duration_constr([Task|Tasks], [StartTime|StartTimes], [FinishTime|FinishTimes]) :-
	task(Task, _, Duration, _),
	FinishTime #= StartTime + Duration,
	duration_constr(Tasks, StartTimes, FinishTimes).

tasks_per_job([], []).
tasks_per_job([Job|Jobs], TasksPerJob) :-
	tasks_per_job(Jobs, TasksPerJobAcc),
	job(Job, Tasks),
	append([Tasks], TasksPerJobAcc, TasksPerJob).

job_constr([], [], []).
job_constr([[_|[]]|Jobs], [_|StartTimes], [_|FinishTimes]) :-
	job_constr(Jobs, StartTimes, FinishTimes).
job_constr([[_|Tasks]|Jobs], [_|StartTimes], [FinishTime|FinishTimes]) :-
	job_constr([Tasks|Jobs], StartTimes, FinishTimes, FinishTime).
job_constr([[_|[]]|Jobs], [StartTime|StartTimes], [_|FinishTimes], PrevTaskFinishTime) :-
	StartTime #>= PrevTaskFinishTime,
	job_constr(Jobs, StartTimes, FinishTimes).
job_constr([[_|Tasks]|Jobs], [StartTime|StartTimes], [FinishTime|FinishTimes], PrevTaskFinishTime) :-
	StartTime #>= PrevTaskFinishTime,
	job_constr([Tasks|Jobs], StartTimes, FinishTimes, FinishTime).

machine_constr([], []).
machine_constr([Task|Tasks], [MachineUsed|MachinesUsed]) :-
	task(Task, MachineType, _, _),
	get_machine_indexes_of_this_type(MachineType, MachineIndexes),
	MachineUsed #:: MachineIndexes,
	machine_constr(Tasks, MachinesUsed).

non_conflict_constr([], [], [], []).
non_conflict_constr([Task|Tasks], [StartTime|StartTimes], [FinishTime|FinishTimes], [MachineUsed|MachinesUsed]) :-
	non_conflict_constr2(Task, StartTime, FinishTime, MachineUsed, Tasks, StartTimes, FinishTimes, MachinesUsed),
	non_conflict_constr(Tasks, StartTimes, FinishTimes, MachinesUsed).

non_conflict_constr2(_, _, _, _, [], [], [], []).
non_conflict_constr2(Task1, StartTime1, FinishTime1, MachineUsed1, [_|Tasks], [StartTime2|StartTimes], [FinishTime2|FinishTimes], [MachineUsed2|MachinesUsed]) :-
	(MachineUsed1 #= MachineUsed2) => (FinishTime1 #=< StartTime2 or FinishTime2 #=< StartTime1),
	non_conflict_constr2(Task1, StartTime1, FinishTime1, MachineUsed1, Tasks, StartTimes, FinishTimes, MachinesUsed).

get_machine_indexes_of_this_type(MachineType, MachineIndexes) :-
	get_all_machines(AllMachines),
	findall(Index, n_th(Index, AllMachines, MachineType), MachineIndexes).

n_th(1, [X|_], X).
n_th(Index1, [_|Xs], Y) :-
	n_th(Index2, Xs, Y),
	Index1 is Index2 + 1.

staff_constr(AllTasks, StartTimes, FinishTimes, 0, Staff) :-
	staff_at_given_time_constr(AllTasks, StartTimes, FinishTimes, 0, Staff, RequiredStaff),
	RequiredStaff #=< Staff.
staff_constr(AllTasks, StartTimes, FinishTimes, Time, Staff) :-
	Time > 0,
	staff_at_given_time_constr(AllTasks, StartTimes, FinishTimes, Time, Staff, RequiredStaff),
	RequiredStaff #=< Staff,
	NewTime is Time - 1,
	staff_constr(AllTasks, StartTimes, FinishTimes, NewTime, Staff).

staff_at_given_time_constr([], [], [], _, _, 0).
staff_at_given_time_constr([Task|Tasks], [StartTime|StartTimes], [FinishTime|FinishTimes], Time, Staff, RequiredStaff) :-
	staff_at_given_time_constr(Tasks, StartTimes, FinishTimes, Time, Staff, RequiredStaffAcc),
	task(Task, _, _, Manpower),
	(StartTime #=< Time and FinishTime #> Time) => (RequiredStaff #= RequiredStaffAcc + Manpower),
	(neg (StartTime #=< Time and FinishTime #> Time)) => (RequiredStaff #= RequiredStaffAcc).

schedule(Jobs, StartTimes, FinishTimes, MachinesUsed, Schedule) :-
	setof(MachineType, machine(MachineType, _), AllMachineTypes),
	get_all_tasks(Jobs, AllTasks),
	schedule_all_types(AllMachineTypes, AllTasks, StartTimes, FinishTimes, MachinesUsed, Schedule).

schedule_all_types([], _, _, _, _, []).
schedule_all_types([MachineType|MachineTypes], AllTasks, StartTimes, FinishTimes, MachinesUsed, Schedule) :-
	get_machine_indexes_of_this_type(MachineType, MachineIndexes),
	schedule_this_type(MachineType, MachineIndexes, AllTasks, StartTimes, FinishTimes, MachinesUsed, ScheduleOfType),
	schedule_all_types(MachineTypes, AllTasks, StartTimes, FinishTimes, MachinesUsed, ScheduleAcc),
	append(ScheduleOfType, ScheduleAcc, Schedule).

schedule_this_type(_, [], _, _, _, _, []).
schedule_this_type(MachineType, [Machine|Machines], AllTasks, StartTimes, FinishTimes, MachinesUsed, ScheduleOfType) :-
	schedule_machine(MachineType, Machine, AllTasks, StartTimes, FinishTimes, MachinesUsed, ScheduleOfMachine),
	sort_schedule_of_machine(ScheduleOfMachine, SortedScheduleOfMachine),
	schedule_this_type(MachineType, Machines, AllTasks, StartTimes, FinishTimes, MachinesUsed, ScheduleOfTypeAcc),
	append(SortedScheduleOfMachine, ScheduleOfTypeAcc, ScheduleOfType).

schedule_machine(MachineType, _, [], [], [], [], ScheduleOfMachine) :-
	append([execs(MachineType, [])], [], ScheduleOfMachine).
schedule_machine(MachineType, Machine, [Task|Tasks], [StartTime|StartTimes], [FinishTime|FinishTimes], [Machine|MachinesUsed], ScheduleOfMachine) :-
	schedule_machine(MachineType, Machine, Tasks, StartTimes, FinishTimes, MachinesUsed, [execs(MachineType, ScheduledTasks)]),
	append([execs(MachineType,[t(Task, StartTime, FinishTime)|ScheduledTasks])], [], ScheduleOfMachine).
schedule_machine(MachineType, Machine, [_|Tasks], [_|StartTimes], [_|FinishTimes], [MachineUsed|MachinesUsed], ScheduleOfMachine) :-
	MachineUsed \= Machine,
	schedule_machine(MachineType, Machine, Tasks, StartTimes, FinishTimes, MachinesUsed, ScheduleOfMachine).

sort_schedule_of_machine([execs(MachineType, ScheduledTasks)], SortedScheduleOfMachine) :-
	sort(2, <, ScheduledTasks, SortedScheduledTasks),
	append([execs(MachineType, SortedScheduledTasks)], [], SortedScheduleOfMachine).

execs(MachineType, []) :-
	machine(MachineType, _).
execs(MachineType, [t(Task, _, _)|Tasks]) :-
	task(Task, MachineType, _, _),
	execs(MachineType, Tasks).

t(Task, Start, Finish) :-
	task(Task, _, Duration, _),
	Finish - Start = Duration.