# simple-frp
Implementation of Krishnaswami's simple-frp paper.

## Installation
Using Stack

## Organization
The actual code lives in `src`. In `app` there is code for building an executable, but that will most likely go away at some point,
since that is not the main goal atm. For now, `app` contains code that is helpful for me when exploring the code in the REPL.

`FRP` is the main module. Currently, `FRP.AST` contains the first swing at an abstract syntax. Still many things that are left out though.

`app/Main.hs` has two examples from the paper hand-encoded into the AST. You can pretty print them using `putStrLn . ppshow` and it
should show a concrete syntax that is close to what is presented in the paper.
