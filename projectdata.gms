$title Process data
$ontext
This file provides data on a variety of tasks observed from videos. Each process is defined in terms of its task. Each task is described by its expected duration for each actor, prerequisites, and delay constraints.
$offtext

$ontext
p1: Low Variation Assembly (Tops)
p2: Low Variation Assembly (Station 3: Drawers)
p3: Case Assembly (Station 1)
p4: Kitting (Station 1)
$offtext
set processes /p1*p4/;
alias(processes, process, p, j);

set tasks /1*25/;
alias(tasks, task, t, t1, t2, k, k1);

* Define mean task durations for a single human operator
table duration(p,t)
	1	2	3	4	5	6	7	8	9	10	11	12	13	14	15	16	17	18	19	20	21	22	23	24	25
p1	2	3	1	3	2	4	2	5	4	3	4	5	11	11	2	1	1	7	1	2	1	-1	-1	-1	-1
p2	1	3	7	1	2	1	1	1	2	1	2	2	1	3	4	5	3	2	-1	-1	-1	-1	-1	-1	-1
p3	2	1	1	4	2	2	1	3	1	1	2	16	-1	-1	-1	-1	-1	-1	-1	-1	-1	-1	-1	-1	-1
p4	2	1	3	1	3	11	3	2	5	3	2	2	1	2	2	4	1	1	3	1	-1	-1	-1	-1	-1
;

set istask(p,t);
istask(p,t) = no;
istask(p,t) = yes$(duration(p,t) gt -1);

* Define predecessors of each task in each job. predecessor(p,t2,t1) = 1 if t1 is a predecessor of t2.
parameter predecessor(p,t2,t1);
predecessor(p,t2,t1)=0;

* Predecessors for process 1
predecessor('p1','3','2')=1;
predecessor('p1','4','1')=2;
predecessor('p1','5','4')=2;
predecessor('p1','7','6')=2;
predecessor('p1','8','7')=2;
predecessor('p1','9','3')=1;
predecessor('p1','9','8')=1;
predecessor('p1','10','9')=1;
predecessor('p1','11','3')=1;
predecessor('p1','11','10')=2;
predecessor('p1','12','3')=1;
predecessor('p1','12','10')=2;
predecessor('p1','13','3')=1;
predecessor('p1','13','10')=2;
predecessor('p1','14','3')=1;
predecessor('p1','14','10')=2;
predecessor('p1','15','11')=2;
predecessor('p1','15','12')=2;
predecessor('p1','15','13')=2;
predecessor('p1','15','14')=2;
predecessor('p1','16','11')=1;
predecessor('p1','16','12')=1;
predecessor('p1','16','13')=1;
predecessor('p1','16','14')=1;
predecessor('p1','17','11')=1;
predecessor('p1','17','12')=1;
predecessor('p1','17','13')=1;
predecessor('p1','17','14')=1;
predecessor('p1','18','17')=2;
predecessor('p1','19','18')=2;
predecessor('p1','20','19')=1;
predecessor('p1','21','11')=1;
predecessor('p1','21','12')=1;
predecessor('p1','21','13')=1;
predecessor('p1','21','14')=1;

* Predecessors for process 2
predecessor('p2','2','1')=2;
predecessor('p2','3','1')=2;
predecessor('p2','3','2')=2;
predecessor('p2','4','3')=2;
predecessor('p2','5','4')=2;
predecessor('p2','6','5')=2;
predecessor('p2','7','6')=2;
predecessor('p2','8','6')=1;
predecessor('p2','8','7')=1;
predecessor('p2','9','8')=2;
predecessor('p2','10','6')=1;
predecessor('p2','10','7')=1;
predecessor('p2','11','7')=1;
predecessor('p2','11','9')=1;
predecessor('p2','12','11')=2;
predecessor('p2','13','9')=1;
predecessor('p2','13','12')=1;
predecessor('p2','14','10')=1;
predecessor('p2','14','13')=2;
predecessor('p2','15','13')=2;
predecessor('p2','16','10')=1;
predecessor('p2','16','13')=2;
predecessor('p2','17','13')=2;
predecessor('p2','18','14')=1;
predecessor('p2','18','15')=1;
predecessor('p2','18','16')=1;
predecessor('p2','18','17')=1;

* Predecessors for process 3
predecessor('p3','2','1')=2;
predecessor('p3','3','2')=2;
predecessor('p3','4','3')=1;
predecessor('p3','5','4')=1;
predecessor('p3','6','4')=1;
predecessor('p3','7','5')=1;
predecessor('p3','7','6')=1;
predecessor('p3','8','7')=2;
predecessor('p3','10','9')=2;
predecessor('p3','11','10')=2;
predecessor('p3','12','8')=1;

* Predecessors for process 4
predecessor('p4','2','1')=2;
predecessor('p4','4','3')=2;
predecessor('p4','5','2')=1;
predecessor('p4','5','4')=2;
predecessor('p4','7','6')=2;
predecessor('p4','8','4')=1;
predecessor('p4','9','8')=2;
predecessor('p4','10','7')=1;
predecessor('p4','10','9')=1;
predecessor('p4','11','10')=2;
predecessor('p4','12','11')=1;
predecessor('p4','13','11')=1;
predecessor('p4','14','2')=1;
predecessor('p4','14','13')=2;
predecessor('p4','15','2')=1;
predecessor('p4','15','12')=2;
predecessor('p4','17','16')=2;
predecessor('p4','18','14')=1;
predecessor('p4','18','17')=1;
predecessor('p4','19','2')=1;
predecessor('p4','19','14')=1;
predecessor('p4','19','15')=1;
predecessor('p4','19','18')=1;
predecessor('p4','20','17')=2;

set ispredecessor(p,t2,t1);
ispredecessor(p,t2,t1) = no;
ispredecessor(p,t2,t1) = yes$(predecessor(p,t2,t1) ge 1);

set sameworkerpredecessor(p,t2,t1);
sameworkerpredecessor(p,t2,t1) = no;
sameworkerpredecessor(p,t2,t1) = yes$(predecessor(p,t2,t1) eq 2);


* Indicate which tasks a robot is capable of performing
table robotCapable(p,t)
	1	2	3	4	5	6	7	8	9	10	11	12	13	14	15	16	17	18	19	20	21	22	23	24	25
p1	0	1	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	1	1	-1	-1	-1	-1
p2	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	1	-1	-1	-1	-1	-1	-1	-1
p3	1	1	1	0	0	0	1	1	1	1	1	1	-1	-1	-1	-1	-1	-1	-1	-1	-1	-1	-1	-1	-1
p4	1	1	1	1	1	1	1	1	1	0	0	1	1	1	1	1	1	0	1	1	-1	-1	-1	-1	-1
;

set isrobottask(p,t);
isrobottask(p,t) = no;
isrobottask(p,t) = yes$(robotCapable(p,t) eq 1);


* Estimate each task duration for a robotic partner
table robotDuration(p,t)
	1	2	3	4	5	6	7	8	9	10	11	12	13	14	15	16	17	18	19	20	21	22	23	24	25
p1	0	1	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	1	1	-1	-1	-1	-1
p2	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	1	-1	-1	-1	-1	-1	-1	-1
p3	1	1	1	0	0	0	1	1	1	1	1	16	-1	-1	-1	-1	-1	-1	-1	-1	-1	-1	-1	-1	-1
p4	1	2	1	1	1	1	2	2	1	0	0	1	1	1	1	3	2	0	1	3	-1	-1	-1	-1	-1
;
