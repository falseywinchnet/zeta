# Failed attempt

The first proof tried to transform an interior-membership hypothesis in place
with `simpa ... at hp`. In this parser position Lean treated the command as a
goal-closing `simpa`, then rejected the trailing `at`. The repair constructed
an explicit `hp' : p ∈ Iio z` with `simpa [interior_Iio] using hp` and passed
that object to the derivative inequality.

No theorem premise or mathematical claim changed.
