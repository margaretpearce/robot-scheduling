$title Class Project, Margaret Pearce
$ontext
This project explores how collaborative robots could be integrated into existing manufacturing processes. Using data from real processes, manufacturing jobs have been broken down into a series of tasks. Each task is described according to its duration as observed in the videos. Prerequisite steps for each task are also documented.

From this data, I explore the tradeoffs of introducing a robotic partner or a human partner on each job. The total task time, active working time of each worker, and task time distribution changes are explored.
$offtext

option limrow=0, limcol=0;
option decimals=4;
option optcr=0.05;
option optca=0.05;
option solprint=off;

$include projectdata.gms

* Command line parameter indicates which process to optimize
$if not set runp $set runp 1

$ontext
Part 1: Data validation for a single human worker
To ensure that the data captured from video is realistic and sufficient to describing each process, the completion time of the job for a single human actor is verified.
$offtext

binary variable rank(p,t,k) 	"task t of process p has position k";
positive variables start(p,k) 	"start time of job in position k of process p";
positive variables comp(p,k) 	"completion time of job in position k of process p";
free variable completion(p)	"completion time for all jobs for process p";
free variable totaljobtime	"total completion time for all jobs";
positive variable pos(p,t)	"position of task t of process p";

equations
onetaskperposition(p,k)		"A single worker can only complete one task at a time",
onepositionpertask(p,t)		"Each task should be assigned to one position",
defcomp(p,k)			"Define the completion time of each task in a job",
defprecedence(p,k)		"Ensure that a task isn't started until the previous task ends",
defpos(p,t)			"Assign each task a position",
defpredecessor(p,t,t1)		"Ensure predecessor relationships are handled",
defcompletion(p,k)		"Define the total process duration",
deftotalcompletion		"Define the total completion time for all jobs combined"
;

onetaskperposition(p,k)..
  sum(t$istask(p,t), rank(p,t,k)) =l= 1;

onepositionpertask(p,t)$istask(p,t)..
  sum(k, rank(p,t,k)) =e= 1;

defcomp(p,k)..
  comp(p,k) =e= start(p,k) + sum(t$istask(p,t), duration(p,t)*rank(p,t,k));

defprecedence(p,k)$(ord(k) lt card(k))..
  start(p,k+1) =g= comp(p,k);

defpos(p,t)$istask(p,t)..
  pos(p,t) =e= sum(k, rank(p,t,k)*ord(k));

* Suppose t is a predecessor of t1. Then the position at which t occurs must be strictly less than than the position of t1.
defpredecessor(p,t,t1)$(ispredecessor(p,t1,t) and istask(p,t) and istask(p,t1))..
  pos(p,t1) =g= pos(p,t) + 1;
  
defcompletion(p,k)..
  completion(p) =g= comp(p,k);

deftotalcompletion..
  totaljobtime =e= sum(p, completion(p));

model humanOnly /all/;
solve humanOnly using mip minimizing totaljobtime;

parameter singleWorkerCompletion(p);
singleWorkerCompletion(p) = completion.l(p);

display completion.l;
display pos.l;




$ontext
Part 2: Multiple human workers
As a next step, we will assign two or more human workers to each process. This will serve as a comparison against the single-human assignment in the Step 1 and in human-robot pairings as in Part 3.
$offtext

set allworkers /h1*h2,r1/;
alias(allworkers,wkr,wkr1);

set humans(allworkers) /h1*h2/;
alias(humans,h,h1);

parameter maxtime(p);
maxtime(p) = sum(t, duration(p,t)$(duration(p,t) ne -1));

set time /time1*time77/;
alias (time, time1, time2);

set data /start_task, end_task, duration_task, assigned_to/;

abort$(card(time) lt smax(p,maxtime(p))) 'Need more values in the time set';

set currentProcess(p);
currentProcess(p) = no;
currentProcess(p) = yes$(ord(p) eq %runp%);
* currentProcess('p1') = yes;
alias(currentProcess, cp, cp1);

binary variable workerdoingtask(p,t,wkr,time)		"1 if worker wkr is executing task t of process p at time";
positive variable compprocess(p)			"The completion time of process p";
free variable compall					"Completion time for all processes";

equations
assignforfullduration(p,t)				"Assign the task over enough time units to cover the full task duration",
maxnumtasksatatime(p,time)				"Max # tasks that can be assigned at a time = # workers",
maxonetaskperworkerpertime(p,wkr,time)			"Each worker can only execute one task in a given time",
maxoneworkerpertask(p,t,time)				"A task can be assigned to at most one person at a given time",
nobreaksintasks(p,t,wkr,time)				"Tasks should not be interrupted or paused",
nosharedtasks(p,t,wkr,time)				"If a worker does one part of a task, the worker does the entire task",
defpredecessortask(p,t,t1,wkr,time)			"Tasks must not begin until their predecessors have completed",
defsameworkerpredecessors(p,t,t1,h,time),
defcompprocess(p,t,wkr,time)				"The entire process p is completed when all tasks in p have been completed",
defcompall						"Define the completion of all current processes"
;

assignforfullduration(cp,t)$istask(cp,t)..
  sum((h,time), workerdoingtask(cp,t,h,time)) =e= duration(cp,t);

maxnumtasksatatime(cp,time)..
  sum((h,t), workerdoingtask(cp,t,h,time)) =l= card(humans);

maxonetaskperworkerpertime(cp,h,time)..
  sum(t, workerdoingtask(cp,t,h,time)) =l= 1;

maxoneworkerpertask(cp,t,time)..
  sum(h, workerdoingtask(cp,t,h,time)) =l= 1;

nobreaksintasks(cp,t,h,time)$(istask(cp,t) and (ord(time) ge 1))..
  (workerdoingtask(cp,t,h,time) - workerdoingtask(cp,t,h,time-1))*duration(cp,t) =l= sum(time1$( (ord(time1) ge ord(time)) and (ord(time1) le (ord(time)+duration(cp,t))) ), workerdoingtask(cp,t,h,time1));

* if workerdoingtask(p,t,h,time)=1, then sum(time1, workerdoingtask(p,t,h,time1)) =g= duration(p,t)
nosharedtasks(cp,t,h,time)$istask(cp,t)..
  workerdoingtask(cp,t,h,time)*duration(cp,t) =l= sum(time1, workerdoingtask(cp,t,h,time1));

* if workerdoingtask(p,t,h,time), then sum(time1$(ord(time1) < ord(time)), workerdoingtask(p,t,h1,time1)) =g= duration(p,t)
defpredecessortask(cp,t,t1,h,time)$(ispredecessor(cp,t1,t) and istask(cp,t) and istask(cp,t1))..
  sum((h1, time1)$(ord(time1) < ord(time)), workerdoingtask(cp,t,h1,time1)) =g= duration(cp,t)*workerdoingtask(cp,t1,h,time);

* predecessor must be completed by the same person
defsameworkerpredecessors(cp,t,t1,h,time)$(ispredecessor(cp,t1,t) and sameworkerpredecessor(cp,t1,t) and istask(cp,t) and istask(cp,t1))..
  sum(time1$(ord(time1) < ord(time)), workerdoingtask(cp,t,h,time1)) =g= duration(cp,t)*workerdoingtask(cp,t1,h,time);

defcompprocess(cp,t,h,time)..
  compprocess(cp) =g= ord(time)*workerdoingtask(cp,t,h,time);
  
compprocess.lo(cp) = ceil(maxtime(cp) / card(humans));
compprocess.up(cp) = maxtime(cp);

defcompall..
  compall =e= sum(cp, compprocess(cp));

* Ignore any tasks with duration -1: this means "no more tasks exist in this job"
workerdoingtask.fx(cp,t,h,time)$(duration(cp,t) eq -1) = 0;

model twoHumans /assignforfullduration, maxnumtasksatatime, maxonetaskperworkerpertime, maxoneworkerpertask, nobreaksintasks, nosharedtasks, defpredecessortask, defsameworkerpredecessors, defcompprocess, defcompall/;
solve twoHumans using mip minimizing compall;

parameter taskHasStarted(p,t,time)		"1 if the task has started by time, otherwise 0";
taskHasStarted(cp,t,time) = 1$(sum((time1,h)$(ord(time1) le ord(time)), workerdoingtask.l(cp,t,h,time1)) ge 1);

parameter startTime(p,t)			"The time that task t of process p starts";
startTime(cp,t) = sum(time, ord(time)*(taskHasStarted(cp,t,time)-taskHasStarted(cp,t,time-1)$(ord(time)>1)));

parameter compTime(p,t)				"The time that task t of process p completes";
compTime(cp,t) = startTime(cp,t) + duration(cp,t)$istask(cp,t);

parameter results(p,t,data)			"Display the start time, end time, duration, and assignment of each task";
results(cp,t,'start_task') = startTime(cp,t)$istask(cp,t);
results(cp,t,'end_task') = compTime(cp,t)$istask(cp,t);
results(cp,t,'duration_task') = duration(cp,t)$istask(cp,t);
results(cp,t,'assigned_to') = sum(h, ord(h)$(sum(time, workerdoingtask.l(cp,t,h,time)) > 0));
display results;

parameter twoHumansCompletion(p)		"The completion time of each process";
twoHumansCompletion(cp) = compprocess.l(cp);
display twoHumansCompletion;

* Show completion time for single worker
display singleWorkerCompletion;

parameter workingTime(p,wkr)			"The total amount of time that worker wkr is active during process p";
workingTime(cp,h) = sum(t, duration(cp,t)$((sum(time, workerdoingtask.l(cp,t,h,time)) > 0) and istask(cp,t))) - sum(time, workerdoingtask.l('p3','12',h,time)); 
display workingTime;

parameter idleTime(p,wkr)			"The percentage of time that worker wkr is not assigned a task throughout process p";
idleTime(cp,h)$(compprocess.l(cp) ne 0) = (compprocess.l(cp) - workingTime(cp,h)) / compprocess.l(cp);
idleTime(cp,h)$(idleTime(cp,h) lt 0.001)=0; 
display idleTime;

parameter timeDecrease(p)			"The percent difference in process completion time between two human workers and one human worker";
timeDecrease(cp) = (singleWorkerCompletion(cp) - compprocess.l(cp)) / singleWorkerCompletion(cp);
timeDecrease(cp)$(timeDecrease(cp) lt 0.001)=0;
display timeDecrease;




$ontext
Part 3: Human and robot teams
Lastly, we will examine the task breakdown for a human worker with a robotic partner. For each process, all tasks have been marked by whether or not the robot is capable of executing the task as-is or with time-negligible modifications. A time estimate on the duration of each task if completed by a robot is also provided.
$offtext

set partners(allworkers) /h1,r1/;
alias(partners,w,w1);

equations
assignforfulldurationpartners(p,t)		"Each task should be assigned for its full duration",
assignforfulldurationhuman(p,t)			"If the human is doing task t, then the human should do it for the full duration",
assignforfulldurationrobot(p,t)			"If the robot is doing task t, then the robot should do it for the full duration",
assignalltasks(p,t)				"Each task should be assigned to a worker",
maxnumtasksatatimepartners(p,time)		"Max # tasks that can be assigned at a time = # workers (2)",
maxonetaskperworkerpertimepartners(p,wkr,time)	"Each worker can only execute one task in a given time",
maxoneworkerpertaskpartners(p,t,time)		"A task can be assigned to at most one worker at a given time",
nobreaksintaskshuman(p,t,time)			"Tasks should not be interrupted or paused (if executed by the human worker)",
nobreaksintasksrobot(p,t,time)			"Tasks should not be interrupted or paused (if executed by the robot worker)"
nosharedtaskshuman(p,t,time)			"If the human worker does one part of a task, he/she does the entire task",
nosharedtasksrobot(p,t,time)			"If the robot worker does one part of a task, it does the entire task",
defpredecessortaskpartners(p,t,t1,time,wkr)	"If a worker is executing task t1 with predecessor t, then t must be 100% complete already by the human or robot",
defsameworkerpredecessorshuman(p,t,t1,time)	"Handle scenario where t1 has predecessor t and both tasks need to be completed by the same worker (human)",
defsameworkerpredecessorsrobot(p,t,t1,time)	"Handle scenario where t1 has predecessor t and both tasks need to be completed by the same worker (robot)",
defcompprocesspartners(p,t,wkr,time)		"The entire process p is completed when all tasks in p have been completed",
defcompallpartners				"Define the completion of all current processes"
;

assignforfulldurationpartners(cp,t)$istask(cp,t)..
  sum((w,time), workerdoingtask(cp,t,w,time)) =l= max(duration(cp,t), robotDuration(cp,t));

assignforfulldurationhuman(cp,t)$istask(cp,t)..
  sum(time, workerdoingtask(cp,t,'h1',time)) =l= duration(cp,t);

assignforfulldurationrobot(cp,t)$istask(cp,t)..
  sum(time, workerdoingtask(cp,t,'r1',time)) =l= robotDuration(cp,t);

assignalltasks(cp,t)$istask(cp,t)..
  sum((w,time), workerdoingtask(cp,t,w,time)) =g= 1;

maxnumtasksatatimepartners(cp,time)..
  sum((w,t), workerdoingtask(cp,t,w,time)) =l= card(partners);

maxonetaskperworkerpertimepartners(cp,w,time)..
  sum(t, workerdoingtask(cp,t,w,time)) =l= 1;

maxoneworkerpertaskpartners(cp,t,time)..
  sum(w, workerdoingtask(cp,t,w,time)) =l= 1;

nobreaksintaskshuman(cp,t,time)$(istask(cp,t) and (ord(time) ge 1))..
  (workerdoingtask(cp,t,'h1',time) - workerdoingtask(cp,t,'h1',time-1))*duration(cp,t) =l= sum(time1$( (ord(time1) ge ord(time)) and (ord(time1) le (ord(time)+duration(cp,t))) ), workerdoingtask(cp,t,'h1',time1));

nobreaksintasksrobot(cp,t,time)$(istask(cp,t) and isrobottask(cp,t) and (ord(time) ge 1))..
  (workerdoingtask(cp,t,'r1',time) - workerdoingtask(cp,t,'r1',time-1))*robotDuration(cp,t) =l= sum(time1$( (ord(time1) ge ord(time)) and (ord(time1) le (ord(time)+robotDuration(cp,t))) ), workerdoingtask(cp,t,'r1',time1));

* if workerdoingtask(p,t,h,time)=1, then sum(time1, workerdoingtask(p,t,h,time1)) =g= duration(p,t)
nosharedtaskshuman(cp,t,time)$istask(cp,t)..
  workerdoingtask(cp,t,'h1',time)*duration(cp,t) =l= sum(time1, workerdoingtask(cp,t,'h1',time1));

nosharedtasksrobot(cp,t,time)$(istask(cp,t) and isrobottask(cp,t))..
  workerdoingtask(cp,t,'r1',time)*robotDuration(cp,t) =l= sum(time1, workerdoingtask(cp,t,'r1',time1));

* if workerdoingtask(p,t1,h,time), then either the robot completed the predecessors or the human did (time units assigned / duration == 1 for human or the robot)
defpredecessortaskpartners(cp,t,t1,time,w)$(ispredecessor(cp,t1,t) and istask(cp,t) and istask(cp,t1))..
  (sum(time1$(ord(time1) < ord(time)), workerdoingtask(cp,t,'h1',time1))/duration(cp,t)) + (sum(time1$(ord(time1) < ord(time)), workerdoingtask(cp,t,'r1',time1))/ (robotDuration(cp,t)$isrobottask(cp,t) + 1$(not isrobottask(cp,t)))) =g= workerdoingtask(cp,t1,w,time);

* predecessor must be completed by the same person
defsameworkerpredecessorshuman(cp,t,t1,time)$(ispredecessor(cp,t1,t) and sameworkerpredecessor(cp,t1,t) and istask(cp,t) and istask(cp,t1))..
  sum(time1$(ord(time1) < ord(time)), workerdoingtask(cp,t,'h1',time1)) =g= duration(cp,t)*workerdoingtask(cp,t1,'h1',time);

* predecessor must be completed by the same person
defsameworkerpredecessorsrobot(cp,t,t1,time)$(ispredecessor(cp,t1,t) and sameworkerpredecessor(cp,t1,t) and istask(cp,t) and istask(cp,t1) and isrobottask(cp,t))..
  sum(time1$(ord(time1) < ord(time)), workerdoingtask(cp,t,'r1',time1)) =g= robotDuration(cp,t)*workerdoingtask(cp,t1,'r1',time);

defcompprocesspartners(cp,t,w,time)..
  compprocess(cp) =g= ord(time)*workerdoingtask(cp,t,w,time);
  
compprocess.lo(cp) = ceil(maxtime(cp) / card(partners));
compprocess.up(cp) = maxtime(cp);

defcompallpartners..
  compall =e= sum(cp, compprocess(cp));

* Ignore any tasks with duration -1
workerdoingtask.fx(cp,t,w,time)$(not istask(cp,t)) = 0;

* If robotCapable(p,t) = 0, don't assign the robot this task (robot is not capable)
workerdoingtask.fx(cp,t,'r1',time)$(not isrobottask(cp,t)) = 0;

model humanRobotPartners /assignforfulldurationpartners, assignforfulldurationhuman, assignforfulldurationrobot, assignalltasks, maxnumtasksatatimepartners, maxonetaskperworkerpertimepartners, maxoneworkerpertaskpartners, nobreaksintaskshuman, nobreaksintasksrobot, nosharedtaskshuman, nosharedtasksrobot, defpredecessortaskpartners, defsameworkerpredecessorshuman, defsameworkerpredecessorsrobot, defcompprocesspartners, defcompallpartners/;
option mip=gurobi;
solve humanRobotPartners using mip minimizing compall;

parameter tasklist(p,t,time,wkr);
tasklist(cp,t,time,w) = workerdoingtask.l(cp,t,w,time);
display tasklist;

parameter taskHasStartedPartners(p,t,time)	"1 if the task has started by time, otherwise 0";
taskHasStartedPartners(cp,t,time) = 1$(sum((time1,w)$(ord(time1) le ord(time)), workerdoingtask.l(cp,t,w,time1)) ge 1);

parameter taskAssignedToRobot(p,t)		"1 if the task is assigned to the robot, otherwise 0";
taskAssignedToRobot(cp,t) = 1$(sum(time1, workerdoingtask.l(cp,t,'r1',time1)) > 0);

parameter startTimePartners(p,t)		"The time that task t of process p starts";
startTimePartners(cp,t) = sum(time, ord(time)*(taskHasStartedPartners(cp,t,time)-taskHasStartedPartners(cp,t,time-1)$(ord(time)>1)));

parameter compTimePartners(p,t)			"The time that task t of process p completes";
compTimePartners(cp,t)$istask(cp,t) = startTimePartners(cp,t) + duration(cp,t)*(1-taskAssignedToRobot(cp,t)) + robotDuration(cp,t)*taskAssignedToRobot(cp,t);

parameter resultsPartners(p,t,data)		"Display the start time, end time, duration, and assignment of each task";
resultsPartners(cp,t,'start_task') = startTimePartners(cp,t)$istask(cp,t);
resultsPartners(cp,t,'end_task') = compTimePartners(cp,t)$istask(cp,t);
resultsPartners(cp,t,'duration_task')$istask(cp,t) = (duration(cp,t)*(1-taskAssignedToRobot(cp,t)) + robotDuration(cp,t)*taskAssignedToRobot(cp,t));
resultsPartners(cp,t,'assigned_to') = 1$(taskAssignedToRobot(cp,t) eq 0) + 2$(taskAssignedToRobot(cp,t) eq 1);
resultsPartners(cp,t,'assigned_to')$(not istask(cp,t)) = 0;
display resultsPartners;

parameter robotPartnerCompletion(p)		"The completion time of each process";
robotPartnerCompletion(cp) = compprocess.l(cp);
display robotPartnerCompletion;

parameter workingTimePartners(p,wkr)		"The total amount of time that worker wkr is active during process p";
workingTimePartners(cp,w) = (sum((t,time), workerdoingtask.l(cp,t,w,time))) - (sum(time1, workerdoingtask.l('p3','12',w,time1))); 
display workingTimePartners;

parameter idleTimePartners(p,wkr)		"The percentage of time that worker wkr is not assigned a task throughout process p";
idleTimePartners(cp,w)$(robotPartnerCompletion(cp) ne 0) = (robotPartnerCompletion(cp) - workingTimePartners(cp,w)) / robotPartnerCompletion(cp);
idleTimePartners(cp,w)$(idleTimePartners(cp,w) lt 0.001)=0; 
display idleTimePartners;

parameter timeDecreasePartnerVsSolo(p)		"The percent difference in process completion time between human/robot partners and one human worker";
timeDecreasePartnerVsSolo(cp) = (singleWorkerCompletion(cp) - robotPartnerCompletion(cp)) / singleWorkerCompletion(cp);
timeDecreasePartnerVsSolo(cp)$(timeDecreasePartnerVsSolo(cp) lt 0.001)=0;
display timeDecreasePartnerVsSolo;

parameter timeDecreasePartnerVsHumans(p)	"The percent difference in process completion time between human/robot partners and two human workers";
timeDecreasePartnerVsHumans(cp) = (twoHumansCompletion(cp) - robotPartnerCompletion(cp)) / twoHumansCompletion(cp);
display timeDecreasePartnerVsHumans;