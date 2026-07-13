#!/usr/bin/env python3
"""Adaptive directed covering for one positive-half-line Jhat rectangle."""

from __future__ import annotations

from dataclasses import dataclass

from flint import arb,ctx

from certify_jhat_cells import mean_value_enclosure
import jet


@dataclass(frozen=True)
class Box:
    lows: tuple[arb,arb,arb]
    highs: tuple[arb,arb,arb]
    depth: int=0


def interval(lo: arb,hi: arb): return arb((lo+hi)/2,((hi-lo)/2).upper())


def split(box: Box,axis: int):
    midpoint=(box.lows[axis]+box.highs[axis])/2
    lows1=list(box.lows); highs1=list(box.highs); highs1[axis]=midpoint
    lows2=list(box.lows); highs2=list(box.highs); lows2[axis]=midpoint
    return Box(tuple(lows1),tuple(highs1),box.depth+1),Box(tuple(lows2),tuple(highs2),box.depth+1)


def main():
    ctx.prec=384; terms=10; tails=jet.tail_bounds(terms+1)
    # m,rho,theta.  The whole rectangle has x=m-theta*rho>0.
    root=Box((arb("0.4"),arb("0.1"),arb("0.1")),(arb("0.8"),arb("0.4"),arb("0.9")))
    root_widths=[float((hi-lo).mid()) for lo,hi in zip(root.lows,root.highs)]
    stack=[root]; certified=0; unresolved=[]; deepest=0; minimum=None
    limit=2000
    while stack:
        box=stack.pop()
        values=[interval(lo,hi) for lo,hi in zip(box.lows,box.highs)]
        try:
            enclosure,_=mean_value_enclosure(*values,terms,tails)
            decided=enclosure.lower()>0
        except (ZeroDivisionError,ValueError):
            decided=False; enclosure=None
        if decided:
            certified+=1; deepest=max(deepest,box.depth)
            lower=enclosure.lower()
            if minimum is None or lower<minimum: minimum=lower
            continue
        if box.depth>=24 or certified+len(stack)+len(unresolved)>=limit:
            unresolved.append(box)
            continue
        scores=[float((hi-lo).mid())/root_widths[j] for j,(lo,hi) in enumerate(zip(box.lows,box.highs))]
        axis=max(range(3),key=lambda j:scores[j])
        left,right=split(box,axis); stack.extend((right,left))
    print(f"rectangle=m[0.4,0.8] rho[0.1,0.4] theta[0.1,0.9]")
    print(f"certified_cells={certified} unresolved={len(unresolved)} deepest={deepest}")
    if minimum is not None: print("minimum_cell_lower=",minimum)
    print("STATUS=", "CERTIFIED" if not unresolved else "INCOMPLETE")


if __name__=="__main__": main()
