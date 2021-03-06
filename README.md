# SportsTimeTabling
This is the course project for the course :IME 639 :Analytics in Transport and Telecom ,offered in 2020-21 II semester at IIT Kanpur.

The aim of the project was to solve the problem statement on sports timetabling from the contest 

ITC 2021:International Timetabling Competition on Sports Timetabling. 
https://www.sportscheduling.ugent.be/ITC2021/index.php

I solved the problem by Integer programming formulation, and implemented in C++ using CPLEX.  The file description for different folders/files in this folder is as below:   

1)The complete visual studios solution/Project can be found in 'sportstimetabling' 

2)Project Report.pdf: This contains introduction ,formulation and complexity analysis  (demonstrated in class) 

3)problem_statement.pdf:contains the complete and detailed problem description along with file format guidelines 

4)Source.cpp: main cpp file contains the complete code ,(also present in sportstimetabling) 

5)Test Input files: contains some test instances(in xml) taken directly from competition site: https://www.sportscheduling.ugent.be/ITC2021/instances.php 

6)Test Output files* :contains solution output to Test input files in xml format 

7)Explanation for break constraints.txt:Explains the formulation &amp;implementation of break constraints which is non intuitive 

The best LB and Best UB for the test instances can be found at : https://www.sportscheduling.ugent.be/ITC2021/instances.php  

The solution file can be validated from : https://www.sportscheduling.ugent.be/ITC2021/validator.php  

All the files satisfies the best LB i.e. produces optimal solution ,and are validated from above, 

Note:1) CPLEX API is required to run the code(used for solving linear/integer/constraint programming  and other OR problems efficiently), can be downloaded directly from IBM site

2)tinxyxml.cpp and tinyxml.h files are required to run the code(read and write inn xml format ).(can be found in /sportstimetabling folder)
