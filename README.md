# busy-beavers

An incomplete, in-progress personal project, aiming to prove that BB(5) = 47176870. To do that we need to enumerate all distinct 5 state turing machines and then prove they halt (easy) or don't halt. Obviously, there is no solution in general to the halting problem, so the program uses heuristic techniques that are effective on machines which have sufficiently simple behavior. 

# Build and run
Get stack, and build with: 

`stack build` 

Select a tactic set from 
`[backward, all, basic, constructive, noncon]`
(see Main.hs) and run

`stack exec busy-beavers-exe tactic input_file output_file`

input_file and output_file are text files, lists of turing machines one per line, eg see `size4_unfinished_18sep.txt`. 
# Features 
* Enumeration of machines using tree normal form
* Run length encoding of tapes
* Detection of cycling machines and Lin recurrence / translated cycling
* Macro machines with fixed-width symbol size
* Heuristic detection of additive (x -> x+3) and affine (x -> 3x+4) machine
  behavior 
* Symbolic best first direct proofs and inductive proofs

## In-progress and Upcoming Features
* Better output of proofs to disk and summary statistics about enumerated machines 
* Abstract interpretation of turing machines in multiple ways
* Performance improvments 
* Additional property tests to ensure correctness

Fair warning that on some commits the tests don't pass, since I will generally write a unit test when I find a bug and sometimes only later fix a bug. In other words, "master" is my personal "develop" branch.