# Preserved failures

## Degree-three Taylor model

A degree-three dependency-aware model certified width-`0.002` cells but became
undecided near width `0.005`.  Raising the model to degree five certifies the
representative width-`0.005` center cell.  Width `0.01` remains undecided and
width `0.02` can include zero in a primitive enclosure.  Brute-force tiling at
those widths would be too large and would not address the unbounded tail.

## Lower-monomial extraction

An attempted fresh expansion of the 1,863-term dominant-theta `J_b` polynomial
to extract a uniform gap monomial was interrupted after two minutes.  The
positive-coefficient theorem remains valid from P000033; this failed expansion
adds no new sign information.  A production route should reuse a serialized
sparse polynomial or perform coefficient extraction before full shifting.

## False compact-core premise

The existing resolved-gap tail lemmas leave an explicit unbounded
near-collision family.  Choosing a numerical cutoff and covering inside it
would silently assume the missing tail theorem.  The global covering step was
therefore not run.
