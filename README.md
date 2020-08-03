
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

./z3 -tr:instance -tr:causality -tr:dummy -tr:triggers -tr:bindings <file.smt2>

* (mandatory) -tr:instance shows the instantiation of quantifiers (e.g. ### 0x2d70a38, quantifier-QID)
* (optional) -tr:dummy shows dummy instantiations. 
A dummy instantiation is easily reduce to true or to sat by Z3 (e.g. forall a:int :: a>=a)

* (optional) -tr:causality shows the matching trigger instantiation of dummy quantifiers. 
A dummy instantiation is easily reduce to true or to sat by Z3 (e.g. forall a:int :: a>=a)
