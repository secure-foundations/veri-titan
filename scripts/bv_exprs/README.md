## building picosat:

I used picosat from: http://fmv.jku.at/picosat/
To enable tracing, I ran this in the extracted folder:

`./configure.sh --trace`

Then to build:

`make`

after building `picosat`, update `PATH` variable to include where `picosat` is located, this is for my laptop:

`export PATH="~/Desktop/research/open_titan/picosat-965/:$PATH"`

## building boolector:

instruction for building boolector can be found here:  
[https://github.com/Boolector/boolector](https://github.com/Boolector/boolector)  
I am using the one with python binding (`./configure.sh --python`)

after building, update `PYTHONPATH` variable, this is for my laptop:

`export PYTHONPATH="~/Desktop/research/open_titan/boolector/build/lib:$PYTHONPATH"`

also update the`PATH` variable to include where `boolector` is located, this is for my laptop:

`export PATH="~/Desktop/research/open_titan/boolector/build/bin/:$PATH"`

## running example:

`python test_proof.py xor 10` will run a 10 bits version of the `xor` test in `bv_exprs.py`.
It will create a smt2 file, a cnf file, a trace file, and a png representing the resolution proof in a `gen` directory. 
The png will be skipped if the graph is too large.
