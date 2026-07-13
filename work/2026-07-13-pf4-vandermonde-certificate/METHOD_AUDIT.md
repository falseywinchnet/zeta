# Audit of the supplied PF5 method

## Evidence boundary

The intended source is CITE2, *The Riemann Kernel is Not a Polya Frequency
Function of Infinite Order*.  Its displayed coordinates were interpreted as
exact terminating decimals and independently evaluated with Arb.  This repairs
the specific witness; it does not validate every error claim in the manuscript.
In particular, the prose description of the geometry does not match the
displayed vectors, and the manuscript's floating-point and coordinate-rounding
accounting is not itself a directed certificate.

The audited coordinates are

```text
X = (0.1727736195, 0.1743710569, 0.1789559107,
     0.1813584361, 0.1841920373)
Y = (0.1764750680, 0.1808082534, 0.1828471610,
     0.1867999444, 0.1899012053).
```

`audit_supplied_witness.py` evaluates the full theta series with a rigorous
tail enclosure at 1024-bit precision.  It proves

```text
D5 = -5.81294786549072031956...e-37  (radius below 3.7e-87)
all 25 order-four subminors: positive
smallest raw order-four lower bound:       3.68617...e-23
smallest Vandermonde-divided lower bound:  585695.853781...
Vandermonde-divided D5:                   -1456189837.3939...
```

The raw determinant magnitudes are misleading: closely spaced nodes force
large Vandermonde factors.  Once those factors are divided out, the PF4
subminors are not close to zero.  The witness therefore demonstrates a real
order-five obstruction while supplying no evidence of an adjacent order-four
obstruction.

## What transfers to PF4

Four parts transfer:

1. Work with unrestricted ordered nodes, not only a Toeplitz or equal-step
   slice.
2. Evaluate the complete theta series and enclose its tail.
3. Divide analytically forced collision zeros before interval arithmetic.
4. Certify continua by directed enclosures of complete parameter cells.

What does not transfer is the sign being sought.  PF5 needs one negative
determinant.  PF4 needs positivity over the entire admissible domain, including
all collision and tail faces.  A finite list of positive evaluations, however
large, cannot provide that conclusion.

The determinant elimination in the witness and the quotient-difference ladder
in the current PF4 pathway are two forms of the same operation: continuous
Neville elimination after forced alternants have been removed.  That is the
useful bridge to the three-point inequality.
