## todo 
A list of things which I would like to do in the project eventually. 

[ ] Property testing 
  [ ] set up Hedgehog 
  [ ] make list of halting and nonhalting machines 
  [ ] test all deciders against the lists 

### Deciders 
[ ] Abstract interpretation
  [ ] nearby tape head 
    [ ] unit test next config
    [ ] integrate in outer loop 
  [ ] halting segment
  [ ] closed regular language deciders
[ ] better derivation of rules for bouncer-in-bouncer and the like 
[ ] experiment: bottom up rules rather than top down rules 
[ ] make guessInductionHypothesis work on the "tricky example" 
[ ] figure out how to reliably decide counters
[ ] improve skiprunsforeverifconsumeslivetape 


### Not-deciders 
[ ] performance improvements 
  [ ] set up profiling (again) (document this time!)
  [ ] remove all linked lists
  [ ] replace checkSeenBefore with a linear time algorithm
[ ] parallelism for large scans
[ ] "branch the search tree" sooner in OuterLoop 
[ ] (maybe) replace "variables must be positive" with "each variable has a lower limit that is tracked separately"
[ ] for macro machines, if there is exactly one rule which can come after a given rule, glue them together

### Quality of life / cleanup 
[ ] remove old or unused code
[ ] remove old comments / organize into docs like this 
[ ] more command line features 
  [ ] start a scan from a seed machine 
[ ] output haltproofs to disk in a readable format
[ ] summary statistics of a scan 
[ ] save intermediate state of a scan to disk