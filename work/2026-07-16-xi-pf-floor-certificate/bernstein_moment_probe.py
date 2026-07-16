#!/usr/bin/env python3
"""Convert the degree-37 endpoint-scaled moment polynomial to Bernstein form."""

from __future__ import annotations

import math
from pathlib import Path

import mpmath as mp


mp.mp.dps = 60


def main() -> None:
    source = Path(__file__).with_name("moment_floor_probe.out")
    terms: list[mp.mpf] = []
    for line in source.read_text().splitlines():
        fields = line.split()
        terms.append(mp.mpf(fields[4]))

    degree = len(terms) - 1
    power = [(-1) ** index * value for index, value in enumerate(terms)]
    bernstein = []
    for k in range(degree + 1):
        value = mp.fsum(
            power[j] * mp.mpf(math.comb(k, j)) / math.comb(degree, j)
            for j in range(k + 1)
        )
        bernstein.append(value)

    for index, value in enumerate(bernstein):
        print(index, mp.nstr(value, 28))
    minimum = min(enumerate(bernstein), key=lambda pair: pair[1])
    print("minimum", minimum[0], mp.nstr(minimum[1], 28))


if __name__ == "__main__":
    main()
