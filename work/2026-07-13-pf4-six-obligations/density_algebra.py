"""Exact compact algebra for the two sufficient PF4 densities."""

from __future__ import annotations

import sympy as sp


def full_density():
    """Return symbols, J_b, and its exactly cleared numerator/denominator."""
    B, C = sp.symbols("B C", positive=True)
    qx, qm, qr = sp.symbols("qx qm qr", positive=True)
    px, pm, pr = sp.symbols("px pm pr")
    ux, vx = sp.symbols("ux vx")
    ML = (qm-qx)/B
    MR = (qr-qm)/C
    NL = (pm-px)/B
    NR = (pr-pm)/C
    fx = px/qx
    fpx = ux/qx-fx**2
    lam = B+C+ML-MR
    tlam = qr-qx+NL-ML**2-NR+MR**2
    D = B+fx-ML
    TD = B*ML+fpx-NL+ML**2
    J = D*lam**2+lam*(D*(fx-ML)+TD)-D*tlam
    Jb = (
        sp.diff(J, B)*qx-sp.diff(J, qx)*px
        -sp.diff(J, px)*ux-sp.diff(J, ux)*vx
    )
    num, den = sp.fraction(sp.cancel(Jb))
    symbols = dict(B=B,C=C,qx=qx,qm=qm,qr=qr,px=px,pm=pm,pr=pr,ux=ux,vx=vx)
    return symbols, sp.factor(Jb), sp.expand(num), sp.factor(den)


def edge_density():
    """Return symbols, S_r, and its exactly cleared numerator/denominator."""
    A = sp.symbols("A", positive=True)
    u0,u1,u2,u3 = sp.symbols("u0:4")
    v0,v1,v2,v3 = sp.symbols("v0:4")
    f = u1/u0
    fp = u2/u0-u1**2/u0**2
    fpp = u3/u0-3*u1*u2/u0**2+2*u1**3/u0**3
    P = u0-fp/2
    Pp = u1-fpp/2
    M = (v0-u0)/A
    N = (v1-u1)/A
    L = A+f-M
    fr = v1/v0
    fpr = v2/v0-v1**2/v0**2
    Q = A+M-fr
    TQ = A*M+(N-M**2)-fpr
    TlogR = fr+TQ/Q-M
    S = 2*L+Pp/P-TlogR

    variables = (A,v0,v1,v2)
    derivatives = (v0,v1,v2,v3)
    Sr = sum(sp.diff(S,z)*dz for z,dz in zip(variables,derivatives))
    num, den = sp.fraction(sp.cancel(Sr))
    symbols = dict(A=A,u0=u0,u1=u1,u2=u2,u3=u3,v0=v0,v1=v1,v2=v2,v3=v3)
    return symbols, sp.factor(Sr), sp.expand(num), sp.factor(den)


def verify_and_report() -> None:
    for name, constructor, terms, expected_den in (
        ("S_r", edge_density, 24, None),
        ("J_b", full_density, 74, None),
    ):
        symbols, expr, num, den = constructor()
        assert sp.cancel(expr-num/den) == 0
        actual = len(sp.Poly(num, *symbols.values()).terms())
        assert actual == terms, (name, actual)
        replacements, reduced = sp.cse(expr, optimizations="basic")
        rebuilt = reduced[0]
        for temporary, value in reversed(replacements):
            rebuilt = rebuilt.xreplace({temporary: value})
        assert sp.cancel(rebuilt-expr) == 0
        print(f"{name}: terms={actual} denominator={den}")
        print(f"{name}: CSE temporaries={len(replacements)} reduced={reduced[0]}")


if __name__ == "__main__":
    verify_and_report()
