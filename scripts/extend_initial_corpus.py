#!/usr/bin/env python3
"""Atomize the second zeta phase of the supplied conversation."""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from mindlib.store import ROOT, Store


def main():
    store = Store(ROOT)
    marker = "Horizontal exponential tilts preserve the sign of every translation-kernel minor."
    if any(f["content"] == marker for f in store.factoids.values()):
        raise SystemExit("extended corpus already seeded")

    def topic(path):
        tid = store.resolve_topic(path)
        if tid is None:
            raise SystemExit(f"missing topic {path}")
        return tid

    # Extend the taxonomy before adding the second evidence layer.
    extra = {}
    for key, parent, label in (
        ("heat", "math/zeta", "debruijn-newman-flow"),
        ("jensen", "math/zeta", "jensen-polynomials"),
        ("twovar", "math/zeta", "two-variable-zeta"),
        ("phase", "math/zeta", "phase-geometry"),
        ("inner", "math/zeta/phase-geometry", "meromorphic-inner-functions"),
        ("ribbon", "math/epistemics/method-barriers", "ribbon-method"),
        ("conditioning", "math/epistemics/method-barriers", "conditioning"),
    ):
        extra[key], _ = store.add_topic(parent, label)

    def cite(author, body, topics, paper, url):
        return store.add_citation(author, body, [topic(t) for t in topics], paper, url)

    c_lagarias = cite(
        "Jeffrey C. Lagarias and Eric Rains",
        "On a Two-Variable Zeta Function for Number Fields, arXiv:math/0104176.",
        ["math/zeta/two-variable-zeta", "math/zeta/riemann-hypothesis"],
        str(ROOT / "tmp" / "lagarias-rains-two-variable-zeta.pdf"),
        "https://arxiv.org/abs/math/0104176",
    )
    c_rt = cite(
        "Brad Rodgers and Terence Tao",
        "The De Bruijn-Newman Constant Is Non-Negative, arXiv:1801.05914.",
        ["math/zeta/debruijn-newman-flow", "math/zeta/riemann-hypothesis"],
        str(ROOT / "tmp" / "rodgers-tao-debruijn-newman.pdf"),
        "https://arxiv.org/abs/1801.05914",
    )
    c_jensen = cite(
        "Michael Griffin, Ken Ono, Larry Rolen, Jesse Thorner, Zachary Tripp, and Ian Wagner",
        "Jensen Polynomials for the Riemann Xi Function, arXiv:1910.01227.",
        ["math/zeta/jensen-polynomials", "math/zeta/riemann-hypothesis"],
        str(ROOT / "tmp" / "jensen-polynomials-xi.pdf"),
        "https://arxiv.org/abs/1910.01227",
    )
    c_convo = "C000001"
    c_pf5 = "C000004"
    c_suzuki = "C000007"

    def sourced(content, topics, *citations):
        fid = store.establish(content, [topic(t) for t in topics])
        for cid in citations:
            store.update_fact(fid, "refer", [cid], citation=True)
        return fid

    def derived(content, topics, *facts):
        return store.establish(content, [topic(t) for t in topics], list(facts))

    f_pf2eq = sourced("For a positive translation kernel, the PF2 condition is equivalent to log-concavity of the generating function.", ["math/zeta/riemann-kernel/polya-frequency/pf2", "math/zeta/riemann-kernel/log-concavity"], c_convo)
    f_example = sourced("The conversation introduces f(x)=exp(-x^2)(1+cos(x)/4), whose Fourier transform is sqrt(pi)exp(-z^2/4)[1+exp(-1/4)cosh(z/2)/4].", ["math/zeta/fourier-analysis", "math/epistemics/method-barriers/ribbon-method"], c_convo)
    f_log = derived("The kernel f(x)=exp(-x^2)(1+cos(x)/4) is strictly log-concave because (log f)'' is at most -2+5/9=-13/9.", ["math/zeta/riemann-kernel/log-concavity", "math/zeta/riemann-kernel/polya-frequency/pf2"], f_example)
    f_nonreal = derived("The Fourier transform of f(x)=exp(-x^2)(1+cos(x)/4) has infinitely many nonreal zeros satisfying cosh(z/2)=-4 exp(1/4).", ["math/zeta/fourier-analysis", "math/epistemics/method-barriers/ribbon-method"], f_example)
    f_pf2sep = derived("Positive, even, Schwartz, strictly PF2 kernels need not have Fourier transforms with only real zeros.", ["math/zeta/riemann-kernel/polya-frequency/pf2", "math/epistemics/method-barriers/ribbon-method"], f_pf2eq, f_log, f_nonreal)

    sourced("The conversation reports that every 3x3 and 4x4 subminor of the supplied 5x5 witness was positive at high precision, while the 5x5 determinant was negative.", ["math/zeta/riemann-kernel/polya-frequency/pf3", "math/zeta/riemann-kernel/polya-frequency/pf4", "math/zeta/riemann-kernel/polya-frequency/pf5", "math/epistemics/evidence-status"], c_convo)
    sourced("The conversation reports broad random, Toeplitz, confluent, and partial-coalescence searches finding no certified negative PF3 or PF4 minor; the referenced search code and data were not supplied.", ["math/zeta/riemann-kernel/polya-frequency/pf3", "math/zeta/riemann-kernel/polya-frequency/pf4", "math/epistemics/evidence-status"], c_convo)
    sourced("Dividing a translation-kernel determinant by its X and Y Vandermonde factors produces a mixed-divided-difference determinant that extends to collision strata and removes automatic coalescence zeros.", ["math/zeta/riemann-kernel/total-positivity", "math/epistemics/method-barriers/conditioning"], c_convo)
    sourced("The conversation reports that the fully confluent order-five obstruction at the origin is the first enlargement of the even derivative block from size 2x2 to 3x3; the odd 2x2 block is unchanged from order four.", ["math/zeta/riemann-kernel/polya-frequency/pf4", "math/zeta/riemann-kernel/polya-frequency/pf5"], c_convo, c_pf5)
    sourced("The conversation gives an analytic-tail argument claiming s0*s4-s2^2>0, s2*s6-s4^2>0, and s0*s4*s8-s0*s6^2-s2^2*s8+2*s2*s4*s6-s4^3<0 at the origin; this proof has not been independently machine-checked in this repository.", ["math/zeta/riemann-kernel/polya-frequency/pf4", "math/zeta/riemann-kernel/polya-frequency/pf5", "math/epistemics/evidence-status"], c_convo)

    f_pf4candidate = sourced("The conversation proposes the finite sequence (1,3,4,2) as PF4 and reports an exhaustive integer-minor certificate, then symmetrizes and Gaussian-smooths it to construct a positive even Schwartz PF4 kernel.", ["math/zeta/riemann-kernel/polya-frequency/pf4", "math/epistemics/method-barriers/ribbon-method", "math/epistemics/evidence-status"], c_convo)
    f_poly = sourced("The generating polynomial 1+3w+4w^2+2w^3=(1+w)(1+2w+2w^2) has nonreal roots (-1±i)/2 off the unit circle, so the proposed smoothed symmetric kernel's Fourier transform would have nonreal zeros if the PF4 premise is valid.", ["math/zeta/fourier-analysis", "math/zeta/riemann-kernel/polya-frequency/pf4"], c_convo)
    derived("The proposed PF4 separator is not yet a repository-established theorem because its exhaustive certificate script and the completeness proof for the enumerated minor window were not supplied.", ["math/zeta/riemann-kernel/polya-frequency/pf4", "math/epistemics/evidence-status"], f_pf4candidate, f_poly)

    sourced(marker, ["math/zeta/riemann-kernel/polya-frequency", "math/zeta/phase-geometry"], c_convo)
    sourced("For Phi_omega(u)=exp(-omega*u)Phi(u), each kxk translation minor equals exp(-omega*sum X)exp(omega*sum Y) times the original minor; therefore every PF order is invariant under a real horizontal xi shift.", ["math/zeta/riemann-kernel/polya-frequency", "math/zeta/phase-geometry"], c_convo)

    sourced("The conversation proposes that, in a topology controlling locally uniform entire Fourier transforms, real-zero kernels form a closed set with empty interior because convolution with a scaled PF4 separator can approach any kernel while importing nonreal zeros.", ["math/epistemics/method-barriers/ribbon-method", "math/zeta/fourier-analysis", "math/epistemics/evidence-status"], c_convo)
    store.establish("Formalize and audit the proposed nowhere-density theorem: specify the kernel topology, prove approximate-identity convergence in it, and independently certify the PF4 separator.", [extra["ribbon"], topic("math/epistemics/evidence-status")])

    f_lambda = sourced("There is a finite de Bruijn-Newman constant Lambda such that H_t has only real zeros exactly for t>=Lambda; RH is equivalent to Lambda<=0.", ["math/zeta/debruijn-newman-flow", "math/zeta/riemann-hypothesis"], c_rt)
    f_nonneg = sourced("Rodgers and Tao prove Lambda>=0.", ["math/zeta/debruijn-newman-flow", "math/zeta/riemann-hypothesis"], c_rt)
    derived("RH is equivalent to Lambda=0.", ["math/zeta/debruijn-newman-flow", "math/zeta/riemann-hypothesis"], f_lambda, f_nonneg)
    sourced("RH is equivalent to hyperbolicity of every Jensen polynomial associated with xi, while each fixed degree is known to be eventually hyperbolic in the shift.", ["math/zeta/jensen-polynomials", "math/zeta/riemann-hypothesis"], c_jensen)

    sourced("Lagarias and Rains construct an entire two-variable xi analogue xi_Q(w,s), recovering completed zeta at w=1 and satisfying xi_Q(w,s)=xi_Q(w,w-s).", ["math/zeta/two-variable-zeta", "math/zeta/riemann-hypothesis"], c_lagarias)
    sourced("For real w, the two-variable critical line is Re(s)=w/2; for negative real w the two-variable xi analogue is positive on that line and is associated with a positive convolution semigroup.", ["math/zeta/two-variable-zeta"], c_lagarias)
    sourced("The conversation reports non-interval-certified numerical thresholds w_PF5≈0.7530406540, w_PF4≈1.3272660075, a zero-pair collision near w≈1.3991687350, and w_PF3≈2.6330487607 in the Lagarias-Rains deformation; code and data were not supplied.", ["math/zeta/two-variable-zeta", "math/zeta/riemann-kernel/polya-frequency", "math/epistemics/evidence-status"], c_convo)

    f_theta = sourced("Suzuki studies Theta_omega(z)=xi(1/2-omega-iz)/xi(1/2+omega-iz) and constructs its associated canonical system unconditionally for omega>1.", ["math/zeta/canonical-systems/suzuki-operator", "math/zeta/phase-geometry/meromorphic-inner-functions"], c_suzuki)
    sourced("For real t, Theta_omega(t) has modulus one by xi's functional equation and conjugation symmetry; meromorphic innerness in the upper half-plane is the stronger property tied to zero-free half-planes.", ["math/zeta/phase-geometry", "math/zeta/phase-geometry/meromorphic-inner-functions"], c_suzuki)
    derived("The supplied program's surviving structural target was to derive positive canonical-system or phase-transport structure from the arithmetic kernel without using sampled zeros or assuming innerness.", ["math/zeta/canonical-systems", "math/zeta/phase-geometry", "math/epistemics/method-barriers"], f_theta)

    sourced("Under the logarithmic unitary map (Uf)(u)=exp(u/2)f(exp u), Suzuki's multiplicative Hankel operator becomes an additive Hankel operator with kernel k_omega(u+v); reflection converts its finite action to convolution form.", ["math/zeta/canonical-systems/suzuki-operator", "math/zeta/computational-experiments/dip-armature"], c_convo, c_suzuki)
    sourced("The DIP experiment's discovery criterion required refinement coherence and sublinear description complexity relative to Gaussian, Blaschke, random all-pass, and generic smooth-phase controls; finite unitary factorization alone was explicitly excluded.", ["math/zeta/computational-experiments/dip-armature", "math/zeta/computational-experiments/phase-law", "math/epistemics/evidence-status"], c_convo)

    store.establish("Reproduce the exact PF2 separator proof in a short checked note and add a direct primary citation for PF2 iff log-concavity.", [topic("math/zeta/riemann-kernel/polya-frequency/pf2"), topic("math/epistemics/evidence-status")])
    store.establish("Independently verify the origin parity-block sign proof with exact or interval arithmetic through the eighth derivative.", [topic("math/zeta/riemann-kernel/polya-frequency/pf5"), topic("math/zeta/interval-arithmetic")])
    store.establish("If the Lagarias-Rains thresholds matter later, recover the missing code and certify each threshold with directed intervals before drawing a bifurcation conclusion.", [topic("math/zeta/two-variable-zeta"), topic("math/zeta/interval-arithmetic")])

    errors = store.validate()
    if errors:
        raise SystemExit("extension validation failed:\n" + "\n".join(errors))
    print(f"extended to {len(store.topics)} topics, {len(store.citations)} citations, {len(store.factoids)} factoids")


if __name__ == "__main__":
    main()
