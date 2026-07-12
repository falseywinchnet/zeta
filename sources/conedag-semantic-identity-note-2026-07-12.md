# ConeDAG semantic identity correspondence

- Author: Quentin Kuttenkuler
- Date: 2026-07-12
- Status: supplied design note; proposals are not established results

## Note

The current ConeDAG audit supports continuity of soft position, exact
subsequence survival counts, locality of contiguous-path damage,
positive-semidefinite feature kernels, conditional bottom-k concentration, and
the ambiguity bound. It does not support semantic equivalence, collision-free
identity, a bi-Lipschitz embedding of edit distance, or lossless
fixed-dimensional compression.

Semantic equivalence is itself a problem of category and content. A human
recognizes that two reports may mean the same thing by understanding what each
statement is about and what it contains. That understanding can be represented
by a reference graph, fragment identity, and colocality. For example, compare:

> The dog fell into blue paint.

with a drunk witness's report:

> The hound, he collapsed into the sky, the oil, the dye!

The comparison invokes relations among *hound* and *dog*, *sky* and *blue*,
*paint* and its constituents, and the witness's impaired reliability. Mapping
*fall* to *collapse* also depends on the event context. Meaning therefore
requires more than fragmentary hypersphere coordinates: it requires the
directional relational role of each fragment—equivalent, operated upon, or
operator—and a representation of the possible intent behind the construction.

On this proposal, identity is content plus intent. A word such as *fall* has a
verb identity in context; more context builds a composite such as
*hound-falling-into-paint*. The same surface token can have multiple identities,
so the truth basis must fork rather than suppress collisions.

Collision-free identity also requires direction and order in the DAG. Order
should decohere smoothly under local changes.

A bi-Lipschitz relation to edit distance cannot by itself encode relevance. A
single comma may radically change a sentence, as in “Let's eat, grandma!”, and
different positions do not have uniform importance. Relevance depends on
context. In extended writing, interpretation generally flows forward; added
context should make lookup more stable.

Lossless fixed-dimensional compression may instead be approached through a
transfer among representational spaces, but human acquisition itself begins as
a lossy map. Meaning, role, and relevance grow through a learned tree or graph.
Fragments inherit meaning from their role and relevance, encoded in edges and
locations.

This suggests that letters, words, and larger fragments belong to several kinds
of trees. Cone hashing should be paired with a dictionary or related identity
system. Individual symbols need stable locations, while semantic relevance is
hereditary. Duplicity must remain possible because one symbol may have multiple
meanings. The resulting trees also need efficient lookup structures; CRT-like
addressing or Huffman-style encodings are possible implementation directions.

