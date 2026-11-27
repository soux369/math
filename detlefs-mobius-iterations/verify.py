#!/usr/bin/env python3
"""Yue's independent verification of Job P: Detlefs's four
Mobius-iteration identities (Nov 16 2010). Exact rational arithmetic;
definitions taken from the OEIS entries themselves."""
from fractions import Fraction as F

def check(name, s0, s0val, step, claimed, nmax):
    s = {s0: F(s0val)}
    for n in range(s0 + 1, nmax + 1):
        s[n] = step(s[n - 1])
    bad = [n for n in range(s0, nmax + 1) if s[n] != claimed(n)]
    print(f"{name}: terms n={s0}..{nmax}, mismatches: {bad}")
    return not bad

ok = True
# (i) A003462: s(0)=0, s(n)=(2s+1)/(s+2), claim a/(a+1), a=(3^n-1)/2
ok &= check("(i) A003462", 0, 0, lambda s: (2*s + 1)/(s + 2),
            lambda n: F((3**n - 1)//2, (3**n - 1)//2 + 1), 30)
# (ii) A007051: s(1)=2, same step, claim a/(a-1), a=(3^n+1)/2
ok &= check("(ii) A007051", 1, 2, lambda s: (2*s + 1)/(s + 2),
            lambda n: F((3**n + 1)//2, (3**n + 1)//2 - 1), 30)
# (iii) A168607: s(1)=5, same step, claim a/(a-4), a=3^n+2
ok &= check("(iii) A168607", 1, 5, lambda s: (2*s + 1)/(s + 2),
            lambda n: F(3**n + 2, 3**n + 2 - 4), 30)
# (iv) A152011: s(1)=2, s(n)=(s+2)/(2s+1), claim a/(a+(-1)^n),
#      a=(3^n-(-1)^n)/2 for n>=1
ok &= check("(iv) A152011", 1, 2, lambda s: (s + 2)/(2*s + 1),
            lambda n: F((3**n - (-1)**n)//2,
                        (3**n - (-1)**n)//2 + (-1)**n), 30)
# OEIS %S prefixes vs the closed forms
assert [(3**n - 1)//2 for n in range(10)] == \
    [0, 1, 4, 13, 40, 121, 364, 1093, 3280, 9841]
assert [(3**n + 1)//2 for n in range(10)] == \
    [1, 2, 5, 14, 41, 122, 365, 1094, 3281, 9842]
assert [3**n + 2 for n in range(10)] == \
    [3, 5, 11, 29, 83, 245, 731, 2189, 6563, 19685]
assert [1] + [(3**n - (-1)**n)//2 for n in range(1, 10)] == \
    [1, 2, 4, 14, 40, 122, 364, 1094, 3280, 9842]
print("OEIS prefixes match the closed forms")
print("ALL CHECKS PASS" if ok else "FAILURES PRESENT")
assert ok
