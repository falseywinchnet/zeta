# Preserved failures

## Mixed derivative-polynomial normalizations

The first new verifier attempt used

`P_0(x)=2x(2x-3)`

together with the recurrence coefficient `5/2-2x`. This double-counted the
factor `e^{2u}` absorbed into `2x`. It produced incorrect even derivatives,
including a negative order-four odd parity block, and the verifier stopped.

There are two correct equivalent choices:

1. Outside factor `2*pi*n^2*exp(5u/2)`, polynomial `P_0=2x-3`, recurrence
   coefficient `5/2-2x`.
2. Outside factor `exp(u/2)`, polynomial `P_0=2x(2x-3)`, recurrence coefficient
   `1/2-2x`.

The retained verifier uses choice 2. No output from the failed run supports a
claim.

## Split prefactor left in the combined evaluator

After correcting the recurrence, the first nonconfluent replay still retained
`exp(5u/2)` from the split normalization while using the combined polynomial.
The origin signs passed because both prefactors equal one at `u=0`, but the
displayed rational witness incorrectly evaluated positive and an order-four
subminor incorrectly evaluated negative. The verifier stopped.

The combined normalization requires `exp(u/2)`. The retained code uses that
prefactor. No nonconfluent output from the failed run supports a claim.

## External interval backend abandoned

An Arb/python-flint verifier successfully enclosed both the printed decimal
witness and the origin parity blocks. It was then abandoned at the user's
direction: it carried more machinery and more computation than the proof
needs. The retained verifier uses only exact `Fraction` arithmetic, three
theta modes, rational Taylor bounds, and an elementary tail estimate. No
Flint output is a premise of the retained result.
