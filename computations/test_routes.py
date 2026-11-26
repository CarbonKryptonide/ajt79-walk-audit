"""Exact stress tests for the three proposed all-dimension arguments.

Run with ordinary Python 3. No search through the Phase 1 midpoint sets.
"""
from collections import Counter
from fractions import Fraction
from itertools import product
from math import comb


def signed_sums(strides, p, allow_holds):
    values = {0}
    signs = (-1, 0, 1) if allow_holds else (-1, 1)
    for t in strides:
        values = {(v + e * t) % p for v in values for e in signs}
    return values


def activation(p):
    # Hyperplane sum z_i = 0. The parity obstruction uses an odd total
    # strictly smaller than p. The last stride is 1 or 2 accordingly.
    size = (p + 1) // 2
    strides = [1] * (size - 1) + [1 if size % 2 else 2]
    assert 0 not in signed_sums(strides, p, False)
    for j, t in enumerate(strides):
        others = strides[:j] + strides[j + 1:]
        assert len(signed_sums(others, p, True)) == p
        assert (-t) % p in signed_sums(others, p, True)

    u, v = (1, 1, 0, 1, 0), (1, -1, 1, 0, 1)
    masks = set()
    for a, b in product(range(p), repeat=2):
        move = tuple((a*x + b*y) % p for x, y in zip(u, v))
        if any(move) and all(z in (0, 1, p-1) for z in move):
            masks.add(tuple(int(z != 0) for z in move))
    assert masks == {(1, 1, 0, 1, 0), (1, 1, 1, 0, 1)}
    # Every mask has m1 = m3 + m4, precluding positive equal marginals.
    assert all(m[0] == m[2] + m[3] for m in masks)


def product_reset(p):
    period = next(k for k in range(1, p) if pow(2, k, p) in (1, p-1))
    w = [0] * p
    w[0] = 2**period - 1
    for k in range(period):
        r = pow(2, k, p)
        w[r] = w[-r] = 2**(period-1-k)
    assert all(w)
    total = sum(w)
    # Law of X+Y under independent reset marginals and the conditional
    # law of X given X+Y=0. Both checks use unnormalized integer masses.
    quotient = [sum(w[a] * w[(y-a) % p] for a in range(p)) for y in range(p)]
    assert len(set(quotient)) > 1
    assert any(total * w[a] * w[-a] != quotient[0] * w[a] for a in range(p))


def bad_scalers(matrix, alphabet, p):
    a, b, c, d = matrix
    inverses = tuple(pow(x, -1, p) for x in alphabet)
    result = set()
    for x, y in product(alphabet, repeat=2):
        r, s = (a*x+b*y) % p, (c*x+d*y) % p
        if r and s:
            result.update((r*i % p, s*j % p) for i, j in product(inverses, repeat=2))
    return result


def overlap():
    p = 79
    alphabet = (18, 19, 20, 22, 25, 32, 42, 65, 73)
    assert all(any(b != a and (2*a-b) % p in alphabet for b in alphabet) for a in alphabet)
    assert {k for k in range(1, p) if {k*x % p for x in alphabet} == set(alphabet)} == {1, 23, 55}
    assert len({x*pow(y, -1, p) % p for x, y in product(alphabet, repeat=2)}) == 15
    assert sum(alphabet) % p == 0
    assert len(bad_scalers((1, 0, 0, 1), alphabet, p)) == 225
    assert len(bad_scalers((1, 1, 1, -1), alphabet, p)) == 1548 > 81**2 // 9

    # Check the second-moment calculation against every 2x2 matrix over F5.
    p, box = 5, (1, 2, 3)
    vectors = {}
    for x, y in product(box, repeat=2):
        vectors.setdefault(y*pow(x, -1, p) % p, (x, y))
    counts = []
    for a, b, c, d in product(range(p), repeat=4):
        counts.append(sum((a*x+b*y) % p in box and (c*x+d*y) % p in box
                          for x, y in vectors.values()))
    prob = Fraction(len(box)**2, p**2)
    mean = len(vectors) * prob
    assert Fraction(sum(counts), len(counts)) == mean
    assert sum((v-mean)**2 for v in counts) / len(counts) == mean*(1-prob)


def integer_product_2d(matrix, p):
    a, b, c, d = matrix
    terms = Counter({(0, 0): 1})
    for u, v in ((1, 0), (0, 1), (a, b), (c, d)):
        updated = terms.copy()
        for (x, y), k in terms.items():
            updated[((x+u) % p, (y+v) % p)] -= k
        terms = updated
    return terms


def lifting(p):
    # In Z[z]/Phi_p, use the length-p cyclic array modulo the relation
    # 1+z+...+z^(p-1)=0. Divisibility by p means equal residues throughout.
    coeff = [1] + [0] * (p-1)
    for _ in range(p-1):
        coeff = [coeff[j] - coeff[j-1] for j in range(p)]
    assert len({x % p for x in coeff}) == 1
    assert len(set(coeff)) > 1

    # Isolate the coefficients with the first p exponents all 1 in the
    # shear matrix of size p+1. Compute the entire remaining cyclic row.
    row = [1] + [0] * (p-1)
    for _ in range(p):
        row = [-(row[j] + row[j-1]) for j in range(p)]
    for _ in range(2):
        row = [row[j] - row[j-1] for j in range(p)]
    k = 4 if p == 7 else 3
    expected = -(comb(p,k)-2*comb(p,k-1)+comb(p,k-2))
    assert row[k] == expected != 0 and row[k] % p == 0
    if p == 79:
        assert row[k] == -72996

    if p <= 13:
        count = 0
        for a, b, c, d in product(range(p), repeat=4):
            if (a*d-b*c) % p:
                terms = integer_product_2d((a,b,c,d), p)
                assert any(k % p for k in terms.values())
                # By homogeneity every torus point in two dimensions is
                # a nonzero multiple of (1,t).
                assert any((a+b*t) % p and (c+d*t) % p for t in range(1,p))
                count += 1
        assert count == (p**2-1)*(p**2-p)
        print(f"F{p}: {count} invertible 2x2 matrices checked")


if __name__ == "__main__":
    for modulus in (5, 7, 11, 13, 79):
        activation(modulus)
        product_reset(modulus)
        lifting(modulus)
    overlap()
    print("Holding-free moves, fractional activation, overlap and lifting checks passed.")
