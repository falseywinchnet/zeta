# Failed sufficient enclosure

The direct transfer of the dominant-theta lower bound to the full theta
kernel was tested with exact rational remainder bounds.  The endpoint
differences were improved from independent absolute errors to the correlated
integral bounds

\[
 |\Delta q^{(j)}(r)-\Delta q^{(j)}(m)|
 \le {K_{j+3}\over8X_m^4}(1-V^{-4}),
\]

and the primitive correction was bounded by the same decaying-gap form.
Nevertheless, an independent box for the remaining derivative errors gives
87 negative shifted coefficients in the `S_r` comparison.  This is not a
negative value of `S_r`: the box still forgets that all errors are successive
derivatives of the single function `log(1+R)`.

The sufficient enclosure is therefore rejected.  The next proof must split
the domain and retain the collision identities: use the explicit full-kernel
collision margins in `prove_full_collision_margins.py` near coalescence, and
use a separated-gap perturbation bound away from it.
