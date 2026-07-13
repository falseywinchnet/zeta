#!/usr/bin/env python3
"""Exact finite certificate for the PF4 sequence (1, 3, 4, 2).

For a_j=0 outside 0<=j<=3, a connected nonzero k-by-k Toeplitz
minor may be translated so its first row index is zero. Connectivity then
forces every consecutive row gap to be at most three, hence the final row
index is at most 3(k-1). A nonzero column lies between zero and three past
the final row, hence at most 3k. Minors outside this window are zero or
factor into smaller connected minors. It is therefore enough to enumerate
the finite windows below for 1<=k<=4.
"""

from fractions import Fraction
from itertools import combinations


SEQUENCE = {0: 1, 1: 3, 2: 4, 3: 2}
EXPECTED_CANDIDATES = {1: 4, 2: 63, 3: 1800, 4: 60060}


def determinant(matrix: list[list[int]]) -> Fraction:
    work = [[Fraction(value) for value in row] for row in matrix]
    sign = Fraction(1)
    for column in range(len(work)):
        pivot = next(
            (row for row in range(column, len(work)) if work[row][column]),
            None,
        )
        if pivot is None:
            return Fraction(0)
        if pivot != column:
            work[column], work[pivot] = work[pivot], work[column]
            sign = -sign
        pivot_value = work[column][column]
        sign *= pivot_value
        for entry in range(column, len(work)):
            work[column][entry] /= pivot_value
        for row in range(column + 1, len(work)):
            multiplier = work[row][column]
            for entry in range(column, len(work)):
                work[row][entry] -= multiplier * work[column][entry]
    return sign


def certify_order(order: int) -> tuple[int, int]:
    if order == 1:
        row_sets = [(0,)]
    else:
        row_sets = (
            (0,) + tail
            for tail in combinations(range(1, 3 * (order - 1) + 1), order - 1)
        )

    candidates = 0
    nonzero = 0
    for rows in row_sets:
        for columns in combinations(range(0, 3 * order + 1), order):
            value = determinant(
                [[SEQUENCE.get(j - i, 0) for j in columns] for i in rows]
            )
            candidates += 1
            if value < 0:
                raise AssertionError(
                    f"negative order-{order} minor: rows={rows}, "
                    f"columns={columns}, determinant={value}"
                )
            nonzero += value != 0
    assert candidates == EXPECTED_CANDIDATES[order]
    return candidates, nonzero


def main() -> None:
    for order in range(1, 5):
        candidates, nonzero = certify_order(order)
        print(f"order={order} candidates={candidates} nonzero={nonzero} negative=0")


if __name__ == "__main__":
    main()
