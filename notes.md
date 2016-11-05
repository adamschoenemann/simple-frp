# Notes

substitution rule as far as I remember it:  
(λx. e)τ = λy. e[x ↦ y]τ

The plan is, as I understand it, to simply rename lambda binders to special
names after parsing, so that we cannot have variable capture in the sense
that free variables become bound when substitution occurs.

Evaluation of (\x. (\y. x y)) (\z. 10 + z) 5:
    (\x. (\y. x y)) (\z. 10 + z) 5 =>
    (\y. (\z. 10 + z) y) 5 =>
    (\z. 10 + z) 5 =>
    10 + 5 => 
    15
    