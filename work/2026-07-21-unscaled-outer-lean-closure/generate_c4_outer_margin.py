#!/usr/bin/env python3
"""Generate exact C4 outer correction polynomials and positivity lemmas."""
import importlib.util, os
from pathlib import Path
os.environ["SYMPY_GROUND_TYPES"]="python"
ROOT=Path(__file__).resolve().parents[2]; HERE=Path(__file__).resolve().parent
s=importlib.util.spec_from_file_location("c",ROOT/"scripts/verify_riemann_signs_core.py")
c=importlib.util.module_from_spec(s); s.loader.exec_module(c); sp=c.sp
def le(e):
 e=sp.expand(e)
 if e.is_Integer: return f"({int(e)} : ℝ)"
 if e.is_Rational: return f"(({int(e.p)} : ℝ)/{int(e.q)})"
 if e==c.x:return "x"
 if e.is_Add:return "("+" + ".join(le(a) for a in e.args)+")"
 if e.is_Mul:return "("+" * ".join(le(a) for a in e.args)+")"
 if e.is_Pow:return f"({le(e.base)} ^ {int(e.exp)})"
 raise ValueError(e)
norm=[sp.cancel((p+4*c.y*p.subs(c.x,4*c.x))/(2*c.x-3)) for p in c.P]
N=c.numerator(sp.cancel(c.raw_h4.subs(dict(zip(c.RAW,norm)))-50_000_000))
yp=sp.Poly(sp.expand(N),c.y)
pieces={k:yp.coeff_monomial(c.y**k) for k in range(5)}
items={"c4MarginBase":pieces[0],"c4MarginNeg1":-pieces[1],
       "c4MarginPos2":pieces[2],"c4MarginNeg3":-pieces[3],
       "c4MarginPos4":pieces[4]}
for k in (1,3):
 B=pieces[0]; M=-pieces[k]
 items[f"c4MarginDecay{k}"]=sp.expand(3*k*M*B-sp.diff(M,c.x)*B+M*sp.diff(B,c.x))
o=["set_option linter.style.header false\nnamespace PF4.UnscaledOuterClosure.C4Data\n"]
for name,e in items.items():
 o.append(f"noncomputable def {name} (x : ℝ) : ℝ :=\n  {le(e)}\n")
 o.append(f"theorem {name}_pos {{x : ℝ}} (hx : 5 ≤ x) : 0 < {name} x := by\n  let z:=x-5\n  have hz : 0≤z := by dsimp [z]; linarith\n  rw [show x=z+5 by dsimp [z]; ring]\n  norm_num [{name}]\n  positivity\n")
o.append("theorem decomposition (x y : ℝ) :\n  PF4.CERT12Inequalities.Generated.c4MarginCorePolynomial x y =\n    c4MarginBase x-c4MarginNeg1 x*y+c4MarginPos2 x*y^2-\n    c4MarginNeg3 x*y^3+c4MarginPos4 x*y^4 := by\n  simp [PF4.CERT12Inequalities.Generated.c4MarginCorePolynomial, c4MarginBase, c4MarginNeg1, c4MarginPos2, c4MarginNeg3, c4MarginPos4]\n  ring\n")
o.append("end PF4.UnscaledOuterClosure.C4Data\n")
(HERE/"C4OuterMarginData.lean").write_text("\n".join(o))
