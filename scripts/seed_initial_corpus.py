#!/usr/bin/env python3
"""Seed the first lossless, status-aware zeta research graph."""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from mindlib.store import ROOT, Store


def main():
    store = Store(ROOT)
    if store.factoids or store.citations:
        raise SystemExit("initial corpus already seeded")

    topics = {"math": "T000001"}

    def branch(key, parent, label):
        topics[key], _ = store.add_topic(topics[parent], label)

    branch("zeta", "math", "zeta")
    branch("rh", "zeta", "riemann-hypothesis")
    branch("xi", "zeta", "xi-function")
    branch("kernel", "zeta", "riemann-kernel")
    branch("fourier", "zeta", "fourier-analysis")
    branch("pf", "kernel", "polya-frequency")
    branch("tp", "kernel", "total-positivity")
    branch("logc", "kernel", "log-concavity")
    branch("pf2", "pf", "pf2")
    branch("pf3", "pf", "pf3")
    branch("pf4", "pf", "pf4")
    branch("pf5", "pf", "pf5")
    branch("pfinf", "pf", "pf-infinity")
    branch("interval", "zeta", "interval-arithmetic")
    branch("canonical", "zeta", "canonical-systems")
    branch("suzuki", "canonical", "suzuki-operator")
    branch("experiments", "zeta", "computational-experiments")
    branch("dip", "experiments", "dip-armature")
    branch("phase", "experiments", "phase-law")
    branch("epistemics", "math", "epistemics")
    branch("status", "epistemics", "evidence-status")
    branch("barriers", "epistemics", "method-barriers")
    branch("unprovability", "epistemics", "unprovability")
    branch("jacobian", "math", "jacobian-conjecture")
    branch("escape", "jacobian", "escape-at-infinity")

    def cite(author, body, topic_keys, paper=None, url=None):
        return store.add_citation(author, body, [topics[k] for k in topic_keys], paper, url)

    c_convo = cite(
        "Anonymous and ChatGPT",
        "Jacobian Conjecture Epistemics conversation, 2026-06-11 through 2026-07-11. "
        "Complete local export: sources/chatgpt-jacobian-conjecture-epistemics.txt; "
        "lossless 278-record index: sources/chatgpt-jacobian-conjecture-epistemics.turns.json.",
        ["zeta", "jacobian", "epistemics"],
    )
    c_user_pf5 = cite(
        "Rainstar",
        "The Riemann Kernel is Not a Polya Frequency Function of Infinite Order, 2025-12-22, supplied manuscript.",
        ["kernel", "pf5", "pfinf"],
        "$HOME/Downloads/The Riemann Kernel is Not a Polya Frequency Function of Infinite Order.pdf",
    )
    c_user_pf2 = cite(
        "Rainstar",
        "Towards the Riemann Hypothesis: Establishing the PF2 Property of the Riemann Kernel, 2025-12-21, supplied manuscript.",
        ["kernel", "pf2", "logc"],
        "$HOME/Downloads/RH is at least PF2.pdf",
    )
    c_pf5 = cite(
        "Wojciech Michałowski",
        "On the Pólya Frequency Order of the de Bruijn-Newman Kernel: Certified Failure at Order Five and the Toeplitz Threshold Phenomenon, arXiv:2602.20313 (2026).",
        ["kernel", "pf5", "interval"],
        str(ROOT / "tmp" / "michalowski-pf5.pdf"),
        "https://arxiv.org/abs/2602.20313",
    )
    c_schoenberg = cite(
        "Alexander Belton, Dominique Guillot, Apoorva Khare, and Mihai Putinar",
        "Preservers of Totally Positive Kernels and Pólya Frequency Functions, arXiv:2110.08206; Theorem 2.2 restates Schoenberg's bilateral-Laplace-transform characterization.",
        ["pf", "pfinf", "tp"],
        str(ROOT / "tmp" / "belton-total-positivity.pdf"),
        "https://arxiv.org/abs/2110.08206",
    )
    c_cv = cite(
        "George Csordas and Richard S. Varga",
        "Moment Inequalities and the Riemann Hypothesis, Constructive Approximation 4 (1988), 175-198, DOI 10.1007/BF02075457.",
        ["kernel", "logc"],
        str(ROOT / "tmp" / "csordas-varga-moment-inequalities.pdf"),
        "https://doi.org/10.1007/BF02075457",
    )
    c_suzuki = cite(
        "Masatoshi Suzuki",
        "A Canonical System of Differential Equations Arising from the Riemann Zeta-Function, arXiv:1204.1827 (2012).",
        ["rh", "canonical", "suzuki"],
        str(ROOT / "tmp" / "suzuki-canonical-system.pdf"),
        "https://arxiv.org/abs/1204.1827",
    )
    c_integral = cite(
        "Masatoshi Suzuki",
        "Integral Operators Arising from the Riemann Zeta Function, arXiv:1907.07302 (2019).",
        ["canonical", "suzuki"],
        str(ROOT / "tmp" / "suzuki-integral-operators.pdf"),
        "https://arxiv.org/abs/1907.07302",
    )

    def sourced(content, topic_keys, *citations):
        fid = store.establish(content, [topics[k] for k in topic_keys])
        for cid in citations:
            store.update_fact(fid, "refer", [cid], citation=True)
        return fid

    def derived(content, topic_keys, *facts):
        return store.establish(content, [topics[k] for k in topic_keys], list(facts))

    f_rh = sourced("RH asserts that all nontrivial zeros of the Riemann xi-function lie on Re(s)=1/2.", ["rh", "xi"], c_suzuki)
    f_xi = sourced("With Xi(t)=xi(1/2+it), RH is equivalent to every zero of Xi being real.", ["rh", "xi"], c_suzuki, c_user_pf2)
    f_fourier = sourced("Xi has a Fourier representation with the even Riemann kernel Phi.", ["xi", "kernel", "fourier"], c_user_pf2, c_cv)
    f_pfdef = sourced("A function is PF_r when every translation-kernel minor det[f(x_i-y_j)] of order at most r is nonnegative for strictly ordered x and y; PF_infinity requires every finite order.", ["pf", "tp"], c_schoenberg, c_user_pf5)
    f_schoen = sourced("Schoenberg's PF_infinity characterization says the bilateral Laplace transform of a PF function equals the reciprocal of a Laguerre-Pólya entire function on its convergence strip, with a converse for the specified Laguerre-Pólya form.", ["pfinf", "fourier"], c_schoenberg)
    f_badbridge = sourced("Both supplied manuscripts state that an even integrable function has Fourier transform with only real zeros if and only if the original function is PF_infinity.", ["pfinf", "rh", "status"], c_user_pf2, c_user_pf5)
    f_bridgeaudit = derived("The manuscripts' stated Fourier-real-zero iff original-kernel-PF_infinity equivalence is not the Schoenberg theorem recorded in F000005.", ["pfinf", "status"], f_schoen, f_badbridge)

    f_userwitness = sourced("The supplied PF5 manuscript reports a negative 5x5 minor near -5.81e-37 using decimal X and Y coordinates and an N=8000 series truncation.", ["pf5", "interval", "status"], c_user_pf5)
    f_geometry = sourced("The PF5 manuscript calls its witness equally spaced with Y=X+delta, but the displayed X spacings vary and displayed Y_i-X_i is not constant.", ["pf5", "status"], c_user_pf5)
    f_error = sourced("The PF5 manuscript bounds infinite-series truncation error but gives no directed enclosure for decimal-coordinate uncertainty or floating-point evaluation of the determinant.", ["pf5", "interval", "status"], c_user_pf5)
    f_uncert = derived("As written, the supplied PF5 manuscript does not certify that its approximately -5.81e-37 determinant remains negative under all stated numerical uncertainties.", ["pf5", "interval", "status"], f_userwitness, f_error)
    f_sr4claim = sourced("The supplied PF5 manuscript claims the global classification SR4 but not PF5.", ["pf4", "pf5", "status"], c_user_pf5)
    f_sr4audit = derived("One negative 5x5 minor proves failure of PF5 and PF_infinity but does not prove global PF4 or SR4.", ["pf4", "pf5", "status"], f_pfdef, f_sr4claim)

    f_certpf5 = sourced("Michałowski certifies a negative Toeplitz 5x5 determinant at u0=0.01 and h=0.05 by interval arithmetic, proving the de Bruijn-Newman kernel is not PF5.", ["pf5", "interval"], c_pf5)
    f_localpf4 = sourced("Michałowski certifies positive Toeplitz minors through order 4 at selected configurations only; global PF4 remains open.", ["pf3", "pf4", "status"], c_pf5)
    f_notinf = derived("The Riemann/de Bruijn-Newman kernel is not PF_infinity.", ["pfinf", "kernel"], f_pfdef, f_certpf5)
    f_barrier = derived("Any RH strategy requiring the original Riemann kernel itself to be PF_infinity is blocked.", ["rh", "pfinf", "barriers"], f_notinf)
    f_notrh = derived("Failure of original-kernel PF_infinity neither disproves RH nor proves RH independent or unprovable, because the claimed equivalence to real zeros is invalid.", ["rh", "unprovability", "status"], f_bridgeaudit, f_notinf)

    f_pf2claim = sourced("The supplied PF2 manuscript claims Phi is strictly log-concave on R and therefore PF2.", ["pf2", "logc", "status"], c_user_pf2)
    f_pf2gap = sourced("The PF2 manuscript's final curvature step uses approximate equalities and says 1200*exp(-3*pi) is about 0.09 while also calling its maximum well below 1e-3; the displayed argument is not a rigorous bound as written.", ["pf2", "logc", "status"], c_user_pf2)
    f_pf2audit = derived("The supplied PF2 manuscript does not establish its global strict-log-concavity claim with the proof currently written.", ["pf2", "logc", "status"], f_pf2claim, f_pf2gap)
    f_cv = sourced("Csordas and Varga prove that log Phi(sqrt(t)) is strictly concave for t>0 and derive moment inequalities related to RH.", ["kernel", "logc"], c_cv)
    f_pfboundary = derived("The supplied corpus establishes a certified upper obstruction at PF5 but does not establish that the kernel's global PF order lies exactly between PF2 and PF3, PF3 and PF4, or PF4 and PF5.", ["pf2", "pf3", "pf4", "pf5", "status"], f_certpf5, f_localpf4, f_pf2audit)

    sourced("The conversation proposes a 'global ribbon' as a sign-control mechanism and conjectures that any such mechanism needs more than PF2.", ["pf2", "barriers", "status"], c_convo)
    sourced("The conversation does not supply a formal definition of ribbon or a proved theorem excluding PF3/PF4 ribbon mechanisms.", ["pf3", "pf4", "barriers", "status"], c_convo)
    sourced("The conversation's claim that zeta is unprovable is presented as an intuition about unbounded discrete complexity, not as a formal independence theorem relative to a named axiomatic system.", ["rh", "unprovability", "status"], c_convo)
    sourced("The useful discrete research question left by the PF work is the exact global Pólya-frequency order of the Riemann kernel, especially global PF3 and PF4.", ["pf3", "pf4", "barriers"], c_convo, c_pf5)

    f_mellin = sourced("The reported DIP experiment passed 12 of 12 Mellin validations with worst relative error 1.35e-81.", ["dip", "suzuki", "status"], c_convo)
    f_hankel = sourced("The reported DIP experiment matched dense Hankel application in 192 of 192 trials with worst relative error 6.14e-16.", ["dip", "suzuki", "status"], c_convo)
    f_fredholm = sourced("At omega=2 and a=1.5, the reported focused closure reached a trace-corrected Fredholm log-m convergence difference of 3.75e-9.", ["suzuki", "experiments", "status"], c_convo)
    f_drift = sourced("After the reported operator convergence, median DIP refinement drift worsened from 0.399 to 0.437.", ["dip", "phase", "status"], c_convo)
    f_rank = sourced("At N=128, the reported 99.9% effective rank was 6 for zeta and 5 for each tested control.", ["dip", "phase", "status"], c_convo)
    f_dipclose = derived("Under the experiment's stated stopping rule, the tested DIP packet basis showed neither a convergent zeta-specific local phase law nor a compression advantage over controls.", ["dip", "phase", "barriers"], f_fredholm, f_drift, f_rank)
    sourced("The DIP experimental claims are preserved only in the conversation export; the referenced source code, CSV/Parquet data, and plots were not supplied with this repository and remain independently unreproduced here.", ["dip", "status"], c_convo)

    sourced("The conversation's durable epistemic method is to name a candidate rigidity principle, construct a finite falsification object, preserve why each attempt fails, and move the surviving boundary into the next round.", ["epistemics", "barriers", "jacobian"], c_convo)
    sourced("The complete conversation source contains 278 prompt/response records and is preserved verbatim plus a lossless JSON turn index with SHA-256 14043e53df1c25afb103ac714ccd0ef7c9ef2d6cd76276d450a05bfa8bbbab66.", ["epistemics", "status"], c_convo)

    store.establish("Repair or replace the supplied PF5 witness with exact rational coordinates and directed interval arithmetic covering coordinates, kernel truncation, rounding, and determinant evaluation.", [topics["pf5"], topics["interval"]])
    store.establish("Determine global PF3 and PF4 status; positivity of selected Toeplitz minors is not enough.", [topics["pf3"], topics["pf4"]])
    store.establish("Formalize 'ribbon' as a mathematical object before testing whether PF2, PF3, or PF4 can support it.", [topics["barriers"], topics["pf2"], topics["pf3"], topics["pf4"]])
    store.establish("Obtain the DIP experiment repository and artifacts before treating its reported numerical closures as independently reproducible.", [topics["dip"], topics["status"]])
    store.establish("Any unprovability claim must name a formal statement and base theory, then prove independence or a precise computability obstruction; divergent numerical difficulty is insufficient.", [topics["unprovability"], topics["status"]])

    errors = store.validate()
    if errors:
        raise SystemExit("seed validation failed:\n" + "\n".join(errors))
    print(f"seeded {len(store.topics)} topics, {len(store.citations)} citations, {len(store.factoids)} factoids")


if __name__ == "__main__":
    main()
