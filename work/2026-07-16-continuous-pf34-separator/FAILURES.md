# Failure ledger

1. Convolution of the discrete PF4 sequence with a Gaussian was not assumed to
   preserve continuous PF4.  No suitable mixed discrete/continuous closure
   theorem was found, and narrower Gaussian mixtures can already fail PF2.
2. Compactly supported Wallis powers provide explicit continuous TN4 kernels,
   but their gamma-product transforms have only real zeros.  They do not
   separate PF4 from Fourier real-rootedness.
3. Uniform support-only cumulant bounds prove PF3 cleanly but are far too loose
   to prove `C4>0`: termwise absolute bounds swamp the Gaussian leading term by
   more than two orders of magnitude.  The exact Euler-polynomial reduction
   replaces that failed estimate.
4. The four-million-point `partial_xi Psi` scan found no PF4 violation.  It is
   retained only as search evidence; it was not promoted into the proof.
5. A first direct SymPy rational-expression expansion of `C4` was abandoned
   because generic cancellation caused expression blowup.  Keeping every
   logarithmic derivative as `N_j/P^j` exposes the common `P^12` denominator
   and finishes in exact polynomial arithmetic.
