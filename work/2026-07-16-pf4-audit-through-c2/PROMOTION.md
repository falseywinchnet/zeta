# Refine-round promotion checklist

1. Diff the candidate manuscript against `paper/manuscript/` and promote the
   accepted text, generated coefficient table, replay tool, requirements lock,
   and release manifest.
2. Correct `CERT2` precision to distinguish the Arb 192-bit base cover from
   the Arb 256-bit/mpmath wrapper checks.
3. Add `python-flint==0.9.0` and Arb 192-bit base-cover precision to `CERT3`
   metadata while retaining the wrapper's exact SymPy/mpmath description.
4. Replay and reseal any certificate whose source record or metadata changes.
5. Add MIND citation boundaries for Dimitrov--Xu if its related-work claim is
   retained; reuse existing `CITE25` for Khare and `CITE6` for Csordas--Varga.
6. Freeze a versioned public release, update the candidate release manifest
   with its tag or DOI, source commit, peak memory, and clean-platform result.
7. Decide the target venue, then obtain truthful identity/contact,
   contribution, funding, and conflict statements from the submitting author.
8. Either migrate to a current tagged-PDF toolchain and repeat full visual QA,
   or document that accessibility tagging is supplied by journal production.
9. Rebuild the maintained root PDF, rerender all pages, search for every stale
   audit phrase, and record the final PDF hash.
10. Retrieve before establishing; integrate this advancement round without
    rewriting or deleting the sibling audit evidence.
