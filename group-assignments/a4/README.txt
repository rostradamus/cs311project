Please fill out each TODO item in the header.

Please don't reformat the HEADER area of this file, and change nothing except the TODOs, particularly nothing before the colon ":" on each line! 

We reserve the right to do (minor) point deductions for misformatted READMEs.

IF MULTIPLE TEAM MEMBERS SUBMIT, ensure that all but one resubmit with nothing but a file named IGNORE.txt.

===================== HEADER ========================

Student #1, Name: Edward Cai
Student #1, ugrad.cs.ubc.ca Login: c4n0b
Student #1, Student Number: 41480154

Student #2, Name: Kwang Hee Park
Student #2, ugrad.cs.ubc.ca Login: m8b9
Student #2, Student Number: 56308133

Student #3, Name: Shobhit Bhatia
Student #3, ugrad.cs.ubc.ca Login: j9k0b
Student #3, Student Number: 23853154

Student #4, Name: Ro Lee
Student #4, ugrad.cs.ubc.ca Login: n3l0b
Student #4, Student Number: 49806102

Student #5, Name: Benjamin Willox
Student #5, ugrad.cs.ubc.ca Login: s2g1b
Student #5, Student Number: 28447150

Team name (for fun!): AliveMau5

Acknowledgment that you understand and have followed the course's collaboration policy (READ IT at
http://www.ugrad.cs.ubc.ca/~cs311/current/_syllabus.php#Collaboration_Policy):

Signed: Edward Cai, Kwang Hee Park, Shobhit Bhatia, Ro Lee, Benjamin Willox

===================== LOGISTICS =====================

Please fill in each of the following:

Approximate hours on the project: 8

Acknowledgment of assistance (per the collab policy!): Referred only to the Racket documentations for help.

For teams, rough breakdown of work:

As a group, we started out with brief meetings to discuss about the tasks: parse and interp. We broke
down the work into 5 parts: Theory questions, parse-begin, interp-begin, interp-infer, and interp-observe.

Each member took one part, completed, and came back as a group to finalize before submission.

====================== THEORY =======================

1. "There are 3 dice: 2 fair dice and a biased die. The distribution
   of the biased die is (1 2 3 3 4 5 6). The three dice are placed in
   a bag, and you draw a die from the bag and roll the die. What is
   the probability that you will roll a 3?"

   Write a program in ISE that computes the answer to the question
   above by inference. Include comments to briefly explain how your
   program works.

   (run '{with {fair {uniform 1 7}} ;;Represents the fair dice
            {with {bias {distribution 1 2 3 3 4 5 6}} ;;Represents the biased die
               {with {diceDist {uniform 1 4}} ;;Represents the 3 dice in bag, 1 and 2 represents fair dice, 3 represents bias die
                  {begin
                     {with {result {infer 1000 {defquery
                                                   {ifelse {> 2 {sample diceDist}} ;;Draw a die from bag, if the die is greater than 2
                                                      {with {die {sample {distribution bias}}} ;;Roll the bias die
                                                         {sample die}}
                                                      {with {die {sample {distribution fair}}} ;;else roll the fair die
                                                         {sample fair}}}}}}
                           {observe result {fun x {= x 3}}}}}}}}) ;;Probability the rolled die is 3

2. In this assignment we keep the weight of the program as a state,
   which we pass around as a parameter and return value, instead of
   just passing it as a parameter like the environment. Give an
   example program in concrete syntax where the interpreter would fail
   to give the correct result (including likelihood!) if we had passed
   the state the same way as the environment. Briefly explain what the
   expected result is, what this improperly implemented interpreter
   would produce, and why.

   An example that we have would be like the following:

   {with {f {fun x {begin
                     {observe {distribution 1 2 3}
                              {fun y {< y 2}}}
                     {> x 3}}}}
         {observe {distribution 1 2 3 4 5} f}}

   From this we would expect the result state to be 2/5, since our implementation
   ignores state changes in functions for observe.

   However, running this improperly implemented program would result
   in the state being 2/15 (1/3 multiplied by 2/5).

   The reason would be that when state is passed around like the environment, 
   it stores / caches the value on a 'global' scope and all the observe values
   would then be accumulated over and create unexpected results as such. 
   

   

    
