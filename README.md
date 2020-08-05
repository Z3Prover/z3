This custom Z3 implementation logs usefull facts about quantifier instatiations into a trace file.

# Z3

## Building Z3 using make and GCC/Clang

Execute:

```bash
python scripts/mk_make.py -d
cd build
make
```
Please note the '-d' at the end of the python command.  
Now you can find the executable of z3 in the folder build.  
For the complete README file please visit https://github.com/Z3Prover/z3.  

## How to run it

The following is the full command line. Below, you can find the meaning of each argument.  

`./z3 -tr:instance -tr:causality -tr:dummy -tr:triggers -tr:bindings <file.smt2>`  

The resulting trace is dumped in a file called `.z3-trace`, you can find the trace file in your working directory.  
Below, we list all the options we support. Each option is going to enable/disable the logging of extra information in the trace file.    

* (mandatory) `-tr:instance` logs the instantiation of quantifiers in the trace.
  (e.g. ### 0x2d70a38, quantifier-QID, Father: #100).  
* (optional) `-tr:dummy` logs dummy instantiations. A dummy instantiation is easily reduce to true or to sat by Z3 (e.g. forall a:int :: a>=a).    
* (optional) `-tr:causality` logs the dependencies among quantifiers. Each instantiation reports a `Father` tag (e.g. Father: #100). Moreover, each instantiation reports the enodes the instantiation is creating (e.g. EN: #100).  
Example of a trace file:  
`### 0x2d70a38, quantifier1, Father: #99`  
`EN: #100`  
`EN: #200`  
`EN: #300`  
`### 0xec49911, quantifier2, Father: #100`  
quantifier1 adds to the egraph the nodes #100, #200 and #300. The node #100 is responsible for the instantiation of quantifier2 (because of the match between ENode and Father tags).    
So, quantifier1 is responsible for the instantiation of quantifier2.  
* (optional) `-tr:bindings` reports the binding associated with each instantiation.  
Example:  
`### 0x2d70a38, quantifier1, Father: #99`  
`0: 15;`  
`1: 99;`  
The quantifier1 has two variables which are instatiated with 15 and 99.  
* (optional) `-tr:triggers` reports the trigger associated with each instantiation.  
Example:  
`### 0x2d70a38, quantifier1, pat: (fun a t), Father: #99`  
The quantifier1 has been triggered by `(fun a t)`.
