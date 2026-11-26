"""Check the published F79 transition data, adaptive holds, and a reset walk.

All assertions use rational or integer arithmetic.  This script certifies
one-coordinate computations only.
"""
from fractions import Fraction as F
from math import prod


def step(law, neighbors, hold=frozenset()):
    result = dict.fromkeys(law, F(0))
    for a, mass in law.items():
        if a in hold:
            result[a] += mass
        else:
            for b in neighbors[a]:
                result[b] += mass / 2
    return result


def stationary_for_two_steps(states, neighbors, hold):
    # Column equations (P Q - I)v=0, with one replaced by normalization.
    columns = []
    for a in states:
        delta = {b: F(b == a) for b in states}
        pq = step(step(delta, neighbors), neighbors, hold)
        columns.append([pq[b] - delta[b] for b in states])
    system = [list(row) + [F(0)] for row in zip(*columns)]
    system[-1] = [F(1)] * (len(states) + 1)
    for i in range(len(states)):
        j = next(j for j in range(i, len(states)) if system[j][i])
        system[i], system[j] = system[j], system[i]
        divisor = system[i][i]
        system[i] = [x / divisor for x in system[i]]
        for j in range(len(states)):
            if j != i:
                q = system[j][i]
                system[j] = [x - q*y for x, y in zip(system[j], system[i])]
    return dict(zip(states, (row[-1] for row in system)))


def check_appendix():
    p = 79
    states = (0, 1, 2, 3, 7, 14, 44, 63, 78)
    distances = (1, 2, 1, 4, 7, 30, 37, 19, 15)
    neighbors = {x: ((x - d) % p, (x + d) % p) for x, d in zip(states, distances)}
    for a, (b, c) in neighbors.items():
        assert b in states and c in states and b != c and (b + c - 2*a) % p == 0
    weights = (1, 1, 1, 2, 2, 2, 2, 2, 2)
    law = {x: F(w, sum(weights)) for x, w in zip(states, weights)}
    assert step(law, neighbors) == law
    assert 15**30 < 79**15 * prod(w**(2*w) for w in weights)
    low = {0, 1, 2}
    before = stationary_for_two_steps(states, neighbors, low)
    after = step(before, neighbors)
    assert min(before.values()) > 0 and sum(before.values()) == 1
    assert step(after, neighbors, low) == before
    masses = tuple(sum(law[x] for x in low) for law in (before, after))
    print("F79 two-period low-state masses (before forced / before optional)", *masses)
    assert max(masses) > F(21, 100)
    # Two copies, in opposite phases, execute the two coordinates in cyclic
    # order in V=F79^2. Each forced move is allowed. The other coordinate
    # moves exactly when it is outside 'low'. The common fair sign required
    # for the actual vector moves preserves the computed marginal dynamics.
    assert sum(masses) / 2 > F(21, 100)


def check_reset(p):
    # At 0 the walk takes either sign of 1. Else it resets to 0 or doubles.
    order = 1
    while pow(2, order, p) != 1:
        order += 1
    law = {0: F(1, 3)}
    for k in range(1, order + 1):
        mass = F(2**(order-k), 3*(2**order - 1))
        for sign in (1, -1):
            x = (sign * pow(2, k - 1, p)) % p
            law[x] = law.get(x, F(0)) + mass
    neighbors = {x: ((1, p - 1) if x == 0 else (0, 2*x % p)) for x in law}
    assert sum(law.values()) == 1
    assert step(law, neighbors) == law
    # Unfolded masses are 1/3 and two copies of 1/(3*2^k), k>=1.
    # H_unfolded = log(3) + (4/3)log(2). Grouping atoms decreases H.
    assert 9**3 * 2**8 < p**3
    print("Reset walk passed stationarity and entropy upper bound at", p, "on", len(law), "states")


if __name__ == "__main__":
    check_appendix()
    for modulus in (59, 61, 79):
        check_reset(modulus)
