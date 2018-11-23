# RuleSpec
Rule Specification Language

11/23/2018

RuleSpec is a Domain Specific Language that enables the specification of nested if-then-else constructs in which
the individual statments are equations with mathematical formulas.  The language was motivated by the requirements
of specifying income tax calculations.  The RuleSpec compiler translates the specification into a web-based 
application with a ruduimentry user interface dialog that elicits the necessary values to perform the computation.
The computation engine is Stanford's Epilog logic programming engine.  A tiny example is included as HelloWord.rspec.

8/20/2018
Completed a basic version of the parser that 
 - handles formulas (ie, translates them to Epilog)
 - generates a rudimentary user interface (emits a worksheet 
   that accepts necessary values, and prints the answers)

To test the code, Simply run ParseRuleSpec.Py. This will produce
RuleSpec\translator\worksheet.html and also print the output on 
console
