# PF4 completion map

State: partial_xi Psi <= 0 (the exact PF4 criterion, R154/R156) is settled on
the positive tail x_xi >= 23 through the Peano reduction: S_r > 0 (R160) and
J_b >= 0 (P000041 cone + P000042 left box + P000043 mean-value strip).

Remaining obligations, in order:

1. Envelope table at x0 = pi. The theta series is n=1-dominated on ALL of
   u >= 0: the relative tail is <= e^{-3 pi} ~ 8.1e-5 at u = 0 and decays
   from there. Rederive tail_error_coefficients (CERT6/7 construction) with
   the floor x0 = pi instead of 23, giving envelopes for w0 >= 2 pi - 3.
   Everything downstream is the same polynomial machinery with a different
   floor and fatter (but still ~1e-4 relative) envelopes.

2. Rerun the positive-branch chain at the new floor: S_r analogue, J_b cone
   radius, left box, mean-value strip, with W_FLOOR = 2 pi - 3 and the new
   table. The Peano density algebra is x-independent; only floors, envelope
   constants, and the transfer margins (LAMBDA_J analogue, eps0 analogue)
   need rederivation. Margins must be re-measured: the criterion scan floor
   is about -4.8 near t = 0 against q ~ 18.7, a ~25% relative margin, so
   1e-4 envelopes have ample room. This settles the criterion for xi >= 0.

3. Mixed sign patterns. For xi < 0 < r the jets at negative points are
   parity transforms (s odd; q, q'' even; q' odd). The criterion's closed
   forms become polynomial certificates in two w-variables (|xi|-side and
   positive side); derive the (-,+,+) and (-,-,+) density analogues with the
   parity signs. Same block/shear/shift machinery.

4. Origin collision cone. Configurations collapsing near u = 0 (mixed-sign
   collisions) are governed by the confluent quantities; C4 >= 1.3e7 on
   [-1,1] and C4 >= 44392 x^6 outside are already certified globally
   (R152), so the cone radius at the origin follows the P000041 pattern
   with the certified floor.

5. Mirror bookkeeping. Evenness maps all-negative configurations to
   all-positive ones through the reversed ECT ladder (minors of an even
   kernel reflect to minors); record the anchor-choice lemma that lets each
   minor use whichever ladder covers its range. With 2-4 this closes every
   sign pattern.

6. Refine audits: P000042, P000043, then the new rounds; integrate the
   criterion theorem into MIND; final statement: the exact global
   Polya-frequency order of the Riemann kernel is four (with R14: not five;
   with R144: at least three; PF4 completes the classification).

Escape behavior needed by 2-3 is already understood: as r -> +infinity the
criterion tends to Lambda_xi(xi,m) <= 0, which is a THEOREM from the
certified q > 0, F2 > 0 (the K-positivity of P000027); as xi -> -infinity it
tends to -q(xi) -> -infinity.
