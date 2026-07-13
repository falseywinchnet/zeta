# Results and status

## Exact advances

- Reduced the full target to `J>=0`, where `J` has a 42-term endpoint
  numerator and `G=q(x)J/B`.
- Proved the generic two-gap collision expansion
  `J=beta(alpha+beta)^2 C4 epsilon^3/(12q^3)+O(epsilon^4)`.
- Reduced the one-sided edge to `E>=0`, then factored
  `E_r=P R S` with `P,R>0`.
- Reduced the edge further to the 24-term density `S_r`; its collision value
  is forced positive by `C4`.
- Derived the 74-term `J_b` density which, if positive, extends the edge to the
  full domain.
- Solved `E,S,S_r,J,J_b` exactly for the exponential tail model.
- Derived an explicit primitive error bound for perturbing interval integrals
  away from that model.

## Diagnostics only

Six named edge configurations gave positive `S`, `S_r`, `E`, and `E_rr` at
80-digit working precision.  Six named full configurations gave positive `J`
and `J_b`.  Coarse and fine differences agreed.  These checks only tested the
two proposed monotonicity lemmas; they are not proof evidence and no sweep was
performed.

## Unresolved

Neither `S_r>=0` nor `J_b>=0` has been proved globally for the Riemann kernel.
Global PF4 therefore remains open.  The round replaces an opaque three-point
rational sign with two explicit endpoint-polynomial densities and exact
collision/tail margins.

