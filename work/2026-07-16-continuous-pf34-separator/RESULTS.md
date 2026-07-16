# Results

Status: raw advancement mathematics; no claim here is a MIND factoid.

## Continuous PF3 and PF4 insufficiency closed in the work layer

`MATHEMATICS.md` gives an explicit positive even Schwartz kernel

`f(x)=exp(-x^2/64) B(exp(x/32))`,

where `B` has coefficients `(2,10,23,30,23,10,2)`.  Uniform cumulant bounds
prove `q>0` and the R141 quantity `F2>0` globally, hence strict PF3.  Exact
polynomial reduction gives `C4=H/P^12`, where the degree-72 palindromic `H`
has 73 strictly positive coefficients.  The generic CERT9 crossing-kernel
identity therefore gives strict PF4.  Its Fourier transform nevertheless has
nonreal zeros because its palindromic Laurent factor reduces to a real cubic
with negative discriminant.

`verify_pf3_separator.py` checks the exact rational PF3 margin and certifies
the negative Fourier discriminant by directed Arb arithmetic.

`verify_pf4_separator.py` constructs the cleared C4 numerator over the exact
rationals and checks every coefficient strictly positive.  A four-million
point floating scan of the complete PF4 transport criterion found no positive
`partial_xi Psi`; its role is exploratory corroboration, not proof.

This removes both continuous insufficiency gaps in the work layer.  A later
refine round must audit the generic CERT9 implication, register the scripts as
a replayable certificate, update MIND, and then revise the maintained paper.
