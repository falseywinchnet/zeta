# PF4 J_b collision radius with preserved faces

- Mode: advancement
- Date: 2026-07-13
- Model: Sydney, OpenAI Codex
- Starting records: R158, R160, R161, CERT6, CERT7
- Starting progress: P000040
- Status: complete as an advancement round; genuine all-order collision radius
  obtained with both angular faces preserved

## Question

Can minimal endpoint integral remainders turn the sparse `J_b` collision
coefficient into a genuine uniform radius while preserving both angular faces?

## Outcome

Yes.  The exact endpoint model terminates at epsilon order 45.  After dividing
every coefficient by `alpha*beta^2`, 40 nonzero remainder orders remain.  Their
complete rational coefficient norm gives

\[
\varepsilon_0=
{46077595453125\over343446590091059391889408}.
\]

For `alpha+beta=1`, `0<=alpha,beta<=1`, and `X_m>=23`, the full-theta cleared
`J_b` numerator is positive for `0<epsilon<=epsilon0`.  The divided extensions
to `beta=0` and `alpha=0` are retained separately; their leading geometry
factors are respectively `1` and `3`.
