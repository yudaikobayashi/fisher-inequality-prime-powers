"""Integral parameters below Fisher's bound, for k <= KMAX.

All (v, k, lam, b, r) of natural numbers with v > k, lam >= 1, b k = v r, r (k-1) = lam (v-1) and b < v
(equivalently lam (v-1) < k (k-1)).  By the main theorem of the notes there are none when k is a prime power.

Writes params.csv (all sets) and table.tex (one row per non-prime-power k: number of sets and the
smallest one).
"""
from sympy import factorint

KMAX = 36
NL = chr(10)
BS = chr(92)


def is_prime_power(k):
    return len(factorint(k)) == 1


rows = []
for k in range(2, KMAX + 1):
    for lam in range(1, k):
        v = k + 1
        while lam * (v - 1) < k * (k - 1):
            if (lam * (v - 1)) % (k - 1) == 0 and (lam * v * (v - 1)) % (k * (k - 1)) == 0:
                b = lam * v * (v - 1) // (k * (k - 1))
                r = lam * (v - 1) // (k - 1)
                assert b * k == v * r and r * (k - 1) == lam * (v - 1) and b < v
                rows.append((k, lam, v, b, r))
            v += 1
rows.sort()
assert all(not is_prime_power(k) for (k, *_) in rows)

with open("params.csv", "w", newline="") as f:
    f.write("k,lambda,v,b,r" + NL)
    for k, lam, v, b, r in rows:
        f.write(f"{k},{lam},{v},{b},{r}" + NL)

out = []
for k in range(2, KMAX + 1):
    if is_prime_power(k):
        continue
    mine = [t for t in rows if t[0] == k]
    _, lam, v, b, r = min(mine, key=lambda t: (t[2], t[1]))
    out.append(f"{k} & {len(mine)} & {v} & {lam} & {b} & {r} " + BS * 2)
with open("table.tex", "w", newline="") as f:
    f.write(NL.join(out) + NL)
print(len(rows), "parameter sets;", len(out), "non-prime-power values of k")
