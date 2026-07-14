#!/usr/bin/env python3
"""Exact coverage audit for the currently proved PF4 tail lemmas."""

from __future__ import annotations

import sympy as sp


def main():
    # P000032 resolved-tail boxes require successive X ratios at least two.
    gap = sp.log(2) / 2
    epsilon = gap / 2
    assert epsilon > 0 and epsilon < gap

    # The family x=M-epsilon, m=M, r=M+epsilon escapes to either tail but
    # never enters a resolved-gap box.  Existing escape results are asymptotic
    # leading terms without a uniform threshold; the dominant one-theta-term
    # theorem has not been transferred to the full kernel near collision.
    M = sp.symbols("M", positive=True)
    x, m, r = M - epsilon, M, M + epsilon
    assert sp.simplify(m - x - epsilon) == 0
    assert sp.simplify(r - m - epsilon) == 0
    assert sp.simplify((m - x) < gap) is sp.true
    assert sp.simplify((r - m) < gap) is sp.true
    print("PASS unresolved near-collision tail family is unbounded")
    print("family=(M-log(2)/4, M, M+log(2)/4), M->infinity")
    print("STATUS=COMPACTIFICATION_NOT_YET_PROVED")


if __name__ == "__main__":
    main()
