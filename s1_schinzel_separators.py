#!/usr/bin/env python3
# Copyright (c) 2026 Riley Betts Ltd
# SPDX-License-Identifier: MIT
"""S1 Schinzel separator sweep (reproduces v0.2 counts).

Band: 1 < m/n < 3, gcd(m,n)=1, n ≤ N (default 40).
A separator is a pair with an explicit mixed-sign integer solution and
no positive solution.  Positive search is complete (x ≤ 3n/m).  Signed
search is bounded (default |coords| ≤ 60); the 86 separators all have
tiny signed witnesses, so that count is not bound-sensitive.

This does not check Brauer–Manin pairings.
"""

from __future__ import annotations

import math
import sys


def pos_solution(m: int, n: int):
    xmin = max(1, (n + m - 1) // m)
    xmax = max(xmin, (3 * n) // m)
    for x in range(xmin, xmax + 1):
        if m * x <= n:
            continue
        den0 = m * x - n
        y0 = max((n * x) // den0 + 1, x)
        y1 = (2 * n * x) // den0
        for y in range(y0, y1 + 1):
            den = m * x * y - n * x - n * y
            if den <= 0:
                continue
            num = n * x * y
            if num % den:
                continue
            z = num // den
            if z >= y:
                return (x, y, z)
    return None


def signed_exists(m: int, n: int, B: int = 60):
    rng = [i for i in range(-B, B + 1) if i]
    for x in rng:
        for y in rng:
            den = m * x * y - n * x - n * y
            if den == 0:
                continue
            num = n * x * y
            if num % den:
                continue
            z = num // den
            if z == 0:
                continue
            if not (x > 0 and y > 0 and z > 0):
                return (x, y, z)
    return None


def sweep(N: int = 40, B: int = 60):
    seps = []
    both_fail = 0
    both_ok = 0
    pos_only = 0
    for n in range(1, N + 1):
        for m in range(n + 1, 3 * n):
            if math.gcd(m, n) != 1:
                continue
            pos = pos_solution(m, n)
            sig = signed_exists(m, n, B)
            if pos and sig:
                both_ok += 1
            elif pos and not sig:
                pos_only += 1
            elif (not pos) and sig:
                seps.append((m, n, sig))
            else:
                both_fail += 1
    return seps, both_fail, both_ok, pos_only


def main() -> int:
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    seps, both_fail, both_ok, pos_only = sweep(N)
    print(f"S1 sweep 1 < m/n < 3, n ≤ {N}")
    print(f"  separators (signed yes, pos no): {len(seps)}")
    print(f"  both fail (signed bound |coord|≤60): {both_fail}")
    print(f"  both ok: {both_ok}")
    print(f"  pos only (no signed inside bound): {pos_only}")
    print(f"  9/5 in separators: {any(m == 9 and n == 5 for m, n, _ in seps)}")
    print("  first 8:", seps[:8])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
