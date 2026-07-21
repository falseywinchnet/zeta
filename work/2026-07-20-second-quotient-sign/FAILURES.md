# Failure ledger

1. The first check unfolded `slopeChord` before unfolding `curvatureMean` and
   `orderThreeRate`; those later definitions reintroduced fresh chord
   denominators. `field_simp` therefore could not use the nonzero chord
   hypotheses and left three rational identities open. The repair unfolds
   container definitions before their components and unfolds the corresponding
   hypotheses explicitly.
2. The direct rate-difference proof left `slopeChord` opaque because it too was
   introduced after the first unfold pass. Reversing the order exposes a
   polynomial identity.
3. The final exact product differed only by multiplication association after
   the Lambda rewrite. A terminal `ring` closes that definitional shape.
4. The failed goals caused the diagnostic declarations to report `sorryAx`.
   This was expected evidence of an incomplete check, not accepted output; the
   final replay must remove it from every printed dependency list.
5. After the unfolding repair, the first-rate identity exposed the cross
   numerator of the logarithmic-slope chord as a new denominator. An explicit
   nonzero bridge did not make the resulting nested fraction normalization
   stable: a later clearing pass reintroduced the same inverse. This entire
   large-rational route was discarded.
6. The replacement proof differentiates the already-proved product
   factorization. Its first check found that pointwise function subtraction
   and lambda subtraction elaborated to different displayed function forms;
   an explicit eventual-equality bridge resolves the mismatch.
7. The replacement's first derivative normalization also omitted the known
   base-point identity `firstQuotD=firstQuot*A`. Naming that identity makes
   the remaining calculation polynomial.
8. An untyped intermediate derivative left its derivative value as a
   metavariable. Giving the chord derivative its complete `HasDerivAt` type
   removed the ambiguity. The next serialized check passed without
   `sorryAx`.
