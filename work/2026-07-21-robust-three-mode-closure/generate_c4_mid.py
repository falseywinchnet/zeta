#!/usr/bin/env python3
"""Generate exact Bernstein certificates for the four missing C4 bands."""
import importlib.util, os
from pathlib import Path
os.environ["SYMPY_GROUND_TYPES"] = "python"
ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("core", ROOT / "scripts/verify_riemann_signs_core.py")
c = importlib.util.module_from_spec(spec); spec.loader.exec_module(c); sp = c.sp

def qr(a):
    a=sp.Rational(a); return str(a.p) if a.q==1 else f"({a.p} / {a.q} : ℚ)"
def rr(a):
    a=sp.Rational(a); return f"({a.p} : ℝ)" if a.q==1 else f"(({a.p} : ℝ) / {a.q})"
def table(poly, lo, hi, den):
    p=sp.Poly(sp.expand(poly.subs({c.x:lo+(hi-lo)*c.w,c.y:c.v/den})),c.w,c.v)
    dx,dy=p.degree(c.w),p.degree(c.v); d={}
    for k in range(dx+1):
      for l in range(dy+1):
        d[k,l]=sp.factor(sum(p.coeff_monomial(c.w**i*c.v**j)*sp.binomial(k,i)/sp.binomial(dx,i)*sp.binomial(l,j)/sp.binomial(dy,j) for i in range(k+1) for j in range(l+1)))
        assert d[k,l]>0
    return dx,dy,d

n=[sp.cancel((p+4*c.y*p.subs(c.x,4*c.x))/(2*c.x-3)) for p in c.P]
margin=c.numerator(sp.cancel(c.raw_h4.subs(dict(zip(c.RAW,n))))-50000000)
bands=[("A",sp.Rational(10,3),sp.Rational(7,2),22000),("B",sp.Rational(7,2),4,36000),("C",4,sp.Rational(9,2),160000),("D",sp.Rational(9,2),5,700000)]
o=["set_option linter.style.header false\nnamespace PF4.RobustThreeModeClosure.Generated\nopen Finset PF4.CERT12Inequalities\n"]
for name,lo,hi,den in bands:
  dx,dy,d=table(margin,lo,hi,den); floor=min(d.values()); cn=f"c4Band{name}Coeff"
  o += [f"def {cn} (i j : ℕ) : ℚ :=\n  match i, j with"]+[f"  | {i}, {j} => {qr(v)}" for (i,j),v in sorted(d.items())]+["  | _, _ => 0\n"]
  o += [f"theorem {cn}_floor : ∀ i ∈ Finset.range ({dx}+1), ∀ j ∈ Finset.range ({dy}+1), {qr(floor)} ≤ {cn} i j := by\n  intro i hi j hj\n  interval_cases i <;> interval_cases j <;> norm_num [{cn}]\n"]
  o += [f"theorem c4Band{name}_representation (u v : ℝ) :\n    PF4.CERT12Inequalities.Generated.c4MarginCorePolynomial ({rr(lo)}+{rr(hi-lo)}*u) ({rr(sp.Rational(1,den))}*v) = bernsteinBoxEval {dx} {dy} {cn} u v := by\n  norm_num [PF4.CERT12Inequalities.Generated.c4MarginCorePolynomial, bernsteinBoxEval, {cn}, bernsteinBasis_eq, Nat.choose]\n  ring\n"]
  o += [f"theorem c4Band{name}_box_pos {{x y : ℝ}} (hx0 : {rr(lo)} ≤ x) (hx1 : x ≤ {rr(hi)}) (hy0 : 0 ≤ y) (hy1 : y ≤ {rr(sp.Rational(1,den))}) : 0 < PF4.CERT12Inequalities.Generated.c4MarginCorePolynomial x y := by\n  let u := (x-{rr(lo)})/{rr(hi-lo)}\n  let v := y/{rr(sp.Rational(1,den))}\n  have hu0 : 0 ≤ u := by dsimp [u]; positivity\n  have hu1 : u ≤ 1 := by dsimp [u]; rw [div_le_one (by norm_num : (0:ℝ)<{rr(hi-lo)})]; linarith\n  have hv0 : 0 ≤ v := by dsimp [v]; positivity\n  have hv1 : v ≤ 1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<{rr(sp.Rational(1,den))})]; exact hy1\n  rw [show x={rr(lo)}+{rr(hi-lo)}*u by dsimp [u]; field_simp; ring, show y={rr(sp.Rational(1,den))}*v by dsimp [v]; field_simp; ring, c4Band{name}_representation]\n  exact bernsteinBoxEval_pos (by norm_num : (0:ℚ)<{qr(floor)}) hu0 hu1 hv0 hv1 {cn}_floor\n"]
def half_table(poly):
  p=sp.Poly(sp.expand(poly.subs({c.x:c.z+5,c.y:c.v/sp.Integer(3000000)})),c.v)
  nv=p.degree(c.v); rows=[]; nz=0
  for j in range(nv+1):
    q=sp.Poly(sp.expand(sum(p.coeff_monomial(c.v**k)*sp.binomial(j,k)/sp.binomial(nv,k) for k in range(j+1))),c.z)
    nz=max(nz,q.degree()); rows.append(q)
  d={(j,k):rows[j].coeff_monomial(c.z**k) for j in range(nv+1) for k in range(nz+1)}
  assert all(v>=0 for v in d.values()) and all(d[j,0]>0 for j in range(nv+1))
  return nv,nz,d

B=[4,40,400,4000,40000,400000,4000000]
for j,p in enumerate(c.P):
  raw=sp.expand(p+4*c.y*p.subs(c.x,4*c.x)); den=2*c.x-3
  for label,poly in [("Upper",B[j]*c.x**j*den-raw),("Lower",B[j]*c.x**j*den+raw)]:
    name=f"baseOuter{j}{label}"; cn=name+"Coeff"; nv,nz,d=half_table(poly); floor=min(d[q,0] for q in range(nv+1))
    o += [f"noncomputable def {name}Polynomial (x y : ℝ) : ℝ := {sp.sstr(poly).replace('**','^')}\n"]
    # Replace SymPy names only after printing the expression.
    o[-1]=o[-1].replace("x", "x").replace("y", "y")
    o += [f"def {cn} (i k : ℕ) : ℚ :=\n  match i, k with"]+[f"  | {a}, {b} => {qr(v)}" for (a,b),v in sorted(d.items())]+["  | _, _ => 0\n"]
    o += [f"theorem {cn}_const_floor : ∀ i ∈ Finset.range ({nv}+1), {qr(floor)} ≤ {cn} i 0 := by\n  intro i hi\n  interval_cases i <;> norm_num [{cn}]\n",
          f"theorem {cn}_nonneg : ∀ i ∈ Finset.range ({nv}+1), ∀ k ∈ Finset.range ({nz}+1), 0 ≤ {cn} i k := by\n  intro i hi k hk\n  interval_cases i <;> interval_cases k <;> norm_num [{cn}]\n",
          f"theorem {name}_representation (v z : ℝ) : {name}Polynomial (z+5) (v/3000000) = bernsteinHalfstripEval {nv} {nz} {cn} v z := by\n  norm_num [{name}Polynomial, bernsteinHalfstripEval, {cn}, bernsteinBasis_eq, Nat.choose]\n  ring\n",
          f"theorem {name}_region_pos {{x y : ℝ}} (hx : 5≤x) (hy0 : 0≤y) (hy1 : y≤1/3000000) : 0 < {name}Polynomial x y := by\n  let v:=y/(1/3000000); let z:=x-5\n  have hv0 : 0≤v := by dsimp [v]; positivity\n  have hv1 : v≤1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<1/3000000)]; exact hy1\n  have hz : 0≤z := by dsimp [z]; linarith\n  have h:=bernsteinHalfstripEval_pos (by norm_num : (0:ℚ)<{qr(floor)}) hv0 hv1 hz {cn}_const_floor {cn}_nonneg\n  rw [← {name}_representation] at h\n  dsimp [v,z] at h\n  convert h using 1 <;> field_simp <;> ring\n"]

o.append("end PF4.RobustThreeModeClosure.Generated\n")
(HERE/"C4MidCertificates.lean").write_text("\n".join(o))
