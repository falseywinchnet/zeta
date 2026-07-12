# Certified result

## Main run

- `a=0.3`
- `mu=1`
- eight normalized Legendre modes
- 176,000 frequency cells of width `0.000125`
- 224-bit Arb precision
- certified frequency cutoff: `22`

| quantity | directed enclosure or bound |
|---|---:|
| finite matrix radius norm | `0.0008728698511504263` |
| complement trace | `0.0002351432298681343` |
| full compact-operator norm upper bound | `0.9962971374103319279` |
| full localized-Weil lower bound | `0.0037028625896680722` |

The P000011 eight-dimensional Ritz upper enclosure was centered at
`0.01011175089124678`. Combining the independently derived directions gives the
certified finite-scale bracket

\[
0.0037028625896680721 < \lambda_{0.3}
< 0.010111750891246784.
\]

The strict upper endpoint may be replaced by the upper endpoint of the P000011
ball when quoted at full precision.

## Coarse repeat

With 44,000 cells of width `0.0005` and 160-bit precision:

| quantity | directed bound |
|---|---:|
| complement trace | `0.0004854454583147653` |
| compact-operator norm upper bound | `0.9991662178114746005` |
| localized-Weil lower bound | `0.0008337821885253995` |

Both runs certify full-operator positivity at this scale. Neither result extends
to `a=0.5`, `a=1`, or the large-scale RH endpoint.

