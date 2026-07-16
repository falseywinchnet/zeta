# Failures and blocked recommendations

## Tagged PDF under the current build engine

A minimal PDF/UA probe using

```tex
\DocumentMetadata{lang=en-US,pdfstandard=ua-2,testphase={phase-III,math}}
```

fails under Tectonic 0.16.9 because `DocumentMetadata` is undefined. The
current engine therefore cannot honestly satisfy the audit's tagged-PDF
request. Promotion should either move the paper build to a current LaTeX PDF
management/tagging toolchain and visually re-audit it, or leave tagging to a
target journal's production workflow. The candidate improves ordinary PDF
metadata but does not claim PDF/UA compliance.

## Human submission fields

Affiliation, legal identity, contact address, ORCID, funding, author
contributions, and conflicts cannot be inferred from the repository. They are
release blockers only when required by the selected venue; no placeholder or
invented declaration should enter the paper.
