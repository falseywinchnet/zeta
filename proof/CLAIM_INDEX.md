# Claim index

| Claim | Paper anchor | MIND / certificate | Obligation | Lean declaration | Status |
|---|---|---|---|---|---|
| Kernel definition/evenness | S02 | R171 context | PO-0001–0007 | unset | CONVENTIONALLY_PROVED |
| `Φ > 0` | S02 | R171 context | PO-0008 | unset | CONVENTIONALLY_PROVED |
| `q > 0` | S03 | R171, CERT12 | PO-0011 | unset | CERTIFIED |
| `F₂ > 0` | S03 | R171, CERT12 | PO-0012 | unset | CERTIFIED |
| `C₄ > 0` | S03 | R171, CERT12 | PO-0013 | unset | CERTIFIED |
| `Λ > 0` | S04 | R141, CERT12 | PO-0015 | unset | CONVENTIONALLY_PROVED |
| strict PF2/PF3 | S04–S05 | R155, R172, CERT5/12 | PO-0016, PO-0043 | unset | CERTIFIED |
| quotient identities | S05 | R154, CERT5 | PO-0017–0019 | unset | SYMBOLICALLY_CHECKED |
| PF4/`∂ξΨ` reduction | S05 | R156, CERT5 | PO-0020 | unset | CONVENTIONALLY_PROVED |
| curvature coordinate | S06 | R153, CERT9 | PO-0021–0025 | unset | CONVENTIONALLY_PROVED |
| sign bridge | S06 | R153, CERT9 | PO-0026–0027 | unset | SYMBOLICALLY_CHECKED |
| `C₄ = Q⁶κ²D` | S07 | R149, CERT9/12 | PO-0028–0029 | unset | CERTIFIED |
| measure normalization | S08 | R153, CERT9 | PO-0030–0031 | `PF4.Measures.muMeasure_univ_eq_one`, `nuMeasure_univ_eq_one` | FORMAL_FRAGMENT |
| transport expectation | S08 | R153, CERT9 | PO-0038 | unset | SYMBOLICALLY_CHECKED |
| strict right mass | S09 | R153, CERT9 | PO-0032 | `PF4.Measures.nuMeasure_Ioc_pos` | FORMAL_FRAGMENT |
| unique density crossing | S09 | R153, CERT9 | PO-0033–0036 | `PF4.Crossing.*`, `PF4.Densities.*` | FORMAL_FRAGMENT |
| strict CDF gap | S09 | R153, CERT9 | PO-0037 | `PF4.CDF.cdfGap_pos`, endpoint theorems | FORMAL_FRAGMENT |
| CDF integration identity | S09 | R153, CERT9 | PO-0039 | unset | CONVENTIONALLY_PROVED |
| positive transport integral | S09 | R153, CERT9 | PO-0040 | `PF4.Transport.concrete_transportNumerator_pos_from_measures` | FORMAL_FRAGMENT |
| `∂ξΨ < 0` | S10 | R153, CERT9 | PO-0041 | `PF4.Transport.partialXiPsi_neg_of_transport` | FORMAL_FRAGMENT |
| strict PF4 | S01/S10 | R164, CERT5/9/12 | PO-0042 | unset | CERTIFIED |
| exact finite PF5 witness | S10 | R179, CERT17 | PO-0044–0045 | unset | CERTIFIED |
| exact order four | S01/S10 | R145 | PO-0046 | unset | CERTIFIED |

The measure and crossing claims were initially downgraded because the scripts'
symbolic checks did not establish them. Their concrete measure, CDF, and
positive-transport core is now Lean-checked. They remain below
`FORMALLY_PROVED` until the upstream curvature-coordinate definitions discharge
the generic regularity/normalization hypotheses and PO-0039 identifies the
expectation difference with the checked weighted integral.
