# Mathematical support for ConeDAG

This note separates proved properties of the representation from empirical
retrieval claims. Hash functions are modeled as random only where stated. The
implementation is deterministic and exact records remain outside the sketch.

## 1. Explicit feature maps

Let a token sequence be \(x=(x_0,\ldots,x_{n-1})\). Before hashing, ConeDAG has
sparse feature maps for lexical content \(C\), local paths \(P\), soft position
\(X\), and shape \(S\). If the nonzero channels are normalized to unit vectors
\(c,p,q,s\), then

\[
F(x)=\frac{\alpha c\oplus\beta p\oplus\gamma q\oplus\delta s}
{\sqrt{\alpha^2+\beta^2+\gamma^2+\delta^2}}.
\]

Consequently,

\[
\langle F(x),F(y)\rangle=
\frac{\alpha^2\langle c_x,c_y\rangle+
\beta^2\langle p_x,p_y\rangle+
\gamma^2\langle q_x,q_y\rangle+
\delta^2\langle s_x,s_y\rangle}
{\alpha^2+\beta^2+\gamma^2+\delta^2}.
\]

Thus there is no cross-channel interference before hash collisions. Each raw
channel inner product is positive semidefinite because it is an explicit feature
map. Signed feature hashing is linear, so the projected inner product remains
positive semidefinite. Unit diagonal normalization preserves this for nonzero
records.

On the unit sphere,
\(\|F(x)-F(y)\|_2=\sqrt{2-2\langle F(x),F(y)\rangle}\). Cone distance is an
ordinary metric on encoded points, not a new metric on strings.

## 2. Soft-position drift

Token \(i\) has relative center \(p_i=(i+1/2)/n\). Delete token \(d\). Every
surviving center moves by less than \(1/(n-1)\):

\[
\left|\frac{i+1/2}{n-1}-\frac{i+1/2}{n}\right|<\frac1{n-1}
\quad(i<d),
\]

and, after reindexing a suffix token,

\[
\left|\frac{i-1/2}{n-1}-\frac{i+1/2}{n}\right|<\frac1{n-1}
\quad(i>d).
\]

The tent map into \(b\) soft bins is continuous and piecewise linear with
Lipschitz constant at most \(2b\). Each survivor's vote changes by \(O(b/n)\),
but there are \(n-1\) survivors. Total channel drift is bounded by \(O(b)\), not
forced to vanish with length. Soft position is smooth yet can reorder close
candidates after deletion.

## 3. Deletion-stable ordered subsequences

Let \(\Phi_r(x)\) be the multiset of all order-preserving subsequences of degree
\(r\). It has \(\binom nr\) occurrence contributions. Deleting one token removes
exactly the subsequences incident to that occurrence:

\[
\binom{n-1}{r-1},\qquad
\frac{\binom{n-1}{r-1}}{\binom nr}=\frac rn.
\]

All other \(\binom{n-1}{r}\) contributions retain the same lexical identity.
After \(t\) deletions the exact surviving fraction is

\[
\frac{\binom{n-t}{r}}{\binom nr}.
\]

This is suffix-invariant: a surviving relation is not renamed when its absolute
index changes. The drift reranker uses degrees two and three. Lodhi et al. provide
the established string-kernel setting in which subsequence counts form an
explicit feature space; these bounds specialize that idea to unweighted deletion
stability.

## 4. Local-path drift

For contiguous token \(k\)-grams, only windows containing a deleted token are
destroyed. At most \(k\) of the original \(n-k+1\) windows are affected, so at
least

\[
\max(0,n-2k+1)
\]

original windows survive unchanged. The disturbance is local, not suffix-wide.
Degrees two through five complement global subsequences: the latter tolerate
deletion, while local paths distinguish crops from reordered near-duplicates.
Winnowing supplies a related local-fingerprint construction and formal match
guarantees; ConeDAG currently bottom-k samples all local paths rather than
adopting winnowing itself.

## 5. Why containment is asymmetric

For feature sets \(A\) from a shorter query and \(B\) from a candidate, define

\[
\operatorname{cont}(A,B)=\frac{|A\cap B|}{|A|}.
\]

If the query is a subsequence of the record, its global ordered features satisfy
\(A\subseteq B\), and containment is one. Symmetric cosine divides by both norms
and penalizes the record for legitimate extra evidence. The reranker therefore
applies containment only when the query is shorter. Equal-length and longer-query
comparisons retain symmetric ConeDAG.

## 6. Bottom-k estimator

Assign each distinct feature an independent continuous random rank and retain the
\(k\) smallest ranks in each set. At comparison, take the \(k\)-th rank of the
sampled union as a common threshold. Conditional on \(m>0\) sampled elements from
\(A\), those elements are a uniform sample without replacement from \(A\). Thus

\[
\widehat C=\frac{\#\{\text{sampled }A\text{ also in }B\}}m
\]

is conditionally unbiased for \(|A\cap B|/|A|\), and the sampling-without-
replacement Hoeffding bound gives

\[
\Pr(|\widehat C-C|\ge\varepsilon\mid m)
\le 2e^{-2m\varepsilon^2}.
\]

If \(A\subseteq B\) and \(m>0\), the estimate is exactly one. A zero-sample event
is possible when \(A\) is small relative to the union; the implementation returns
zero rather than inventing evidence. Stratifying global order and local paths
prevents the larger order family from starving local samples.

The code uses deterministic 128-bit BLAKE2b ranks. These probability claims apply
under the ideal independent-rank model, not as a cryptographic proof about fixed
BLAKE2b outputs.

## 7. Feature-hashing boundary

For an ideal signed hash projection \(H\), pairwise-independent buckets and
zero-mean independent signs give

\[
\mathbb E\langle Hu,Hv\rangle=\langle u,v\rangle.
\]

Weinberger et al. establish concentration results for the hashing trick under
specified random-hash assumptions. ConeDAG's BLAKE2b selection is a deterministic
engineering surrogate. Seed ablations measure its behavior; they do not turn the
ideal-model theorem into a theorem about this fixed hash.

## 8. Erasure ambiguity

Let \(y\) have length \(n-1\), and let \(a\) be an erased token. Inserting \(a\)
at any of \(n\) positions produces a parent at deletion distance one from \(y\).
No function of \(y\) alone can identify which parent generated it. Under a
uniform prior its success probability is at most \(1/n\).

Retrieval evaluation must admit every minimum-edit parent unless external context
selects one. Strict source-ID accuracy is still reported, but it is not called
reconstruction when the observation is information-theoretically ambiguous.

## 9. Support boundary

Supported: continuity of soft position, exact subsequence survival counts,
locality of contiguous-path damage, positive-semidefinite feature kernels,
conditional bottom-k concentration, and the ambiguity bound.

Not supported: semantic equivalence, collision-free identity, a bi-Lipschitz
embedding of edit distance, or lossless fixed-dimensional compression.
Belazzougui and Zhang solve a parameterized edit-recovery problem with different
objectives and substantially more structure; ConeDAG is not an implementation of
that result.
