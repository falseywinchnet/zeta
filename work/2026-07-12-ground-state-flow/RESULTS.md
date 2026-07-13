# Results

## Full-operator propagation

Below the first prime threshold, the scaled localized-Weil forms differ by an
explicit scalar and a bounded smooth-kernel operator. Centering the kernel flow
at its negative constant mode yields

`lambda_b >= lambda_a-log(b/a)-(13/4)(b-a)`

for `0.3<=a<=b<(log 2)/2`.

Using the certified `a=0.3` anchor gives

`lambda_a >= 0.00001619592300140549920561302118133333333`

for every `a in [0.3,0.30056]`.

This extends full localized-Weil positivity analytically beyond the certified
scale.

## Arithmetic thresholds

A new prime-power translation enters through two endpoint strips whose width is
`ell=2-log(n)/a`. The boundary term already present in the positive logarithmic
form gives the relative estimate

`|P_{n,a}(w)| <= [4 Lambda(n)/sqrt(n)]`

`/ log(1/(2ell)) * L(w)`.

The coefficient tends to zero at the threshold. Prime ramps are therefore
continuous in the correct form topology; their apparent `L2` operator-norm jump
is not the relevant geometry.

## Structural gain

The ground-state curve now has:

1. a certified positive point;
2. an explicit one-sided analytic flow inequality;
3. a proved positive interval;
4. a threshold-entry modulus tied to logarithmic boundary energy;
5. the source-normalized inequality
   `E_log<=L+(2/pi-gamma)||.||^2`;
6. an explicit form-continuity modulus for every active translation;
7. a piecewise comparison architecture of the form
   `q_b>=(1-eta)q_a-K||.||^2`.
