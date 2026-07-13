#!/usr/bin/env python3
"""Finite max-flow diagnostics for structured arithmetic allocations."""

from __future__ import annotations

import importlib.util
import pathlib
import sys

import networkx as nx
import numpy as np


HERE=pathlib.Path(__file__).resolve().parent
SOURCE=HERE.parent/"2026-07-12-arithmetic-sign-criterion"/"sign_probe.py"
SPEC=importlib.util.spec_from_file_location("sign_probe",SOURCE)
PROBE=importlib.util.module_from_spec(SPEC);sys.modules[SPEC.name]=PROBE
assert SPEC.loader is not None;SPEC.loader.exec_module(PROBE)


def prime_mask(limit: int) -> np.ndarray:
    result=np.ones(limit+1,dtype=bool);result[:2]=False
    for p in range(2,int(limit**0.5)+1):
        if result[p]:result[p*p::p]=False
    return result


def allocation_ratio(omega: float,limit: int,prime_pool: bool=False) -> float:
    c=PROBE.coefficients(omega,limit)
    n=np.arange(1,limit+1);kernel=PROBE.kernel(omega,n/limit)
    lows=n[kernel<0];highs=n[kernel>0]
    demand=-c[lows]*kernel[lows-1];supply=c[highs]*kernel[highs-1]
    prime=prime_mask(limit)
    graph=nx.DiGraph();source="source";sink="sink";infinity=float(demand.sum())
    for index,value in zip(lows,demand):
        graph.add_edge(source,("low",int(index)),capacity=float(value))
    for index,value in zip(highs,supply):
        graph.add_edge(("high",int(index)),sink,capacity=float(value))
    for index in lows:
        allowed=(highs%index==0)
        if prime_pool:allowed|=prime[highs]
        for high in highs[allowed]:
            graph.add_edge(("low",int(index)),("high",int(high)),capacity=infinity)
    value=nx.maximum_flow_value(
        graph,source,sink,flow_func=nx.algorithms.flow.preflow_push
    )
    return value/float(demand.sum())


def main() -> None:
    print("omega,x,divisibility,divisibility_plus_primes")
    for omega in (0.1,0.25,0.4):
        for limit in (100,300,1000,3000):
            direct=allocation_ratio(omega,limit)
            pooled=allocation_ratio(omega,limit,prime_pool=True)
            print(f"{omega},{limit},{direct:.12g},{pooled:.12g}")


if __name__=="__main__":main()
