"""Exact enumeration of smallest midpoint sets, their affine orbits and invariants.

Only Python's standard library is needed.  Run with --help for the options.
"""
import argparse
from collections import Counter
from itertools import combinations, product
import json
from math import prod, log, exp, gcd
from pathlib import Path


def canonical(points, p):
    """Lexicographically first image containing 0 and 1 is first over all images."""
    candidates = (
        tuple(sorted((x - a) * inv % p for x in points))
        for a in points for b in points if b != a
        for inv in (pow((b - a) % p, -1, p),)
    )
    return min(candidates)


def enumerate_sets(p, bound):
    """Find every minimum orbit if bound is at least the true minimum.

    Every valid set has an affine image containing -1,0,1.  At a partial
    set choose an unsupported midpoint. Any valid extension must contain
    both endpoints of one of its possible pairs. Branch over all such
    pairs that fit the bound. A minimum set cannot strictly extend a
    valid set, so stopping as soon as the set is valid loses no minimum.
    """
    pairs = [tuple(((a - t) % p, (a + t) % p) for t in range(1, (p + 1) // 2))
             for a in range(p)]
    reps = set()
    best = bound
    seen = set()

    def search(points):
        nonlocal best
        key = sum(1 << a for a in points)
        if key in seen or len(points) > best:
            return
        seen.add(key)
        for a in points:
            if not any(b != a and (2 * a - b) % p in points for b in points):
                break
        else:
            if len(points) < best:
                best = len(points)
                reps.clear()
            reps.add(canonical(points, p))
            return
        room = best - len(points)
        if room == 1:
            for b in points - {a}:
                search(points | {(2 * a - b) % p})
        elif room >= 2:
            for b, c in pairs[a]:
                search(points | {b, c})

    search(frozenset((p - 1, 0, 1)))
    return sorted(reps)


def midpoint_options(points, p):
    return [
        [(i, j) for i, j in combinations(range(len(points)), 2)
         if (points[i] + points[j] - 2 * a) % p == 0]
        for a in points
    ]


def determinant(matrix):
    """Integer Bareiss elimination."""
    matrix = [row.copy() for row in matrix]
    sign = 1
    divisor = 1
    for i in range(len(matrix) - 1):
        if matrix[i][i] == 0:
            pivot = next((j for j in range(i + 1, len(matrix)) if matrix[j][i]), None)
            if pivot is None:
                return 0
            matrix[i], matrix[pivot] = matrix[pivot], matrix[i]
            sign = -sign
        scale = matrix[i][i]
        for j in range(i + 1, len(matrix)):
            for k in range(i + 1, len(matrix)):
                matrix[j][k] = (scale * matrix[j][k] - matrix[j][i] * matrix[i][k]) // divisor
        divisor = scale
    return sign * matrix[-1][-1]


def stationary_weights(policy):
    """Principal Laplacian cofactors span the stationary vector."""
    size = len(policy)
    lap = [[0] * size for _ in policy]
    for i, (b, c) in enumerate(policy):
        lap[i][i] = 2
        lap[i][b] = lap[i][c] = -1
    weights = [
        determinant([row[:i] + row[i + 1:] for j, row in enumerate(lap) if i != j])
        for i in range(size)
    ]
    if min(weights) <= 0:
        return None
    divisor = gcd(*weights)
    weights = [w // divisor for w in weights]
    for i, w in enumerate(weights):
        assert 2 * w == sum(v for v, pair in zip(weights, policy) if i in pair)
    return weights


def entropy_policy(points, p):
    options = midpoint_options(points, p)
    count = 0
    best = None
    for policy in product(*options):
        weights = stationary_weights(policy)
        if weights is None:
            continue
        count += 1
        total = sum(weights)
        # exp(2H) = (total^(2*total) / prod(w^(2*w)))^(1/total)
        numerator = total ** (2 * total)
        denominator = prod(w ** (2 * w) for w in weights)
        if best:
            bn, bd, btotal, *_ = best
            if numerator ** btotal * bd ** total >= bn ** total * denominator ** btotal:
                continue
        best = (numerator, denominator, total, weights, policy)
    assert best is not None
    numerator, denominator, total, weights, policy = best
    return {
        "policies": count,
        "stationary_weights": weights,
        "endpoint_pairs": [[points[i], points[j]] for i, j in policy],
        "exp_2H_approx": exp(2 * (log(total) - sum(w * log(w) for w in weights) / total)),
        "exp_2H_lt_p_exact": numerator < p ** total * denominator,
    }


def invariants(points, p):
    size = len(points)
    differences = Counter((a - b) % p for a in points for b in points)
    sums = Counter((a + b) % p for a in points for b in points)
    translated_product_sizes = Counter()
    for center in range(p):
        translated = [(a - center) % p for a in points]
        translated_product_sizes[len({a * b % p for a in translated for b in translated})] += 1
    intersections = Counter()
    lookup = set(points)
    for scale in range(1, p):
        overlaps = Counter((a - scale * b) % p for a in lookup for b in lookup)
        intersections.update(overlaps.get(shift, 0) for shift in range(p))
    return {
        "points": points,
        "affine_stabilizer_size": intersections[size],
        "orbit_size": p * (p - 1) // intersections[size],
        "difference_support_size": len(differences),
        "difference_multiplicity_histogram_nonzero_shifts": dict(sorted(Counter(
            differences[d] for d in range(1, p)).items())),
        "sum_support_size": len(sums),
        "additive_energy": sum(count ** 2 for count in differences.values()),
        "translated_product_support_size_histogram": dict(sorted(translated_product_sizes.items())),
        "affine_self_intersection_histogram": dict(sorted(intersections.items())),
        "best_stationary_policy": entropy_policy(points, p),
    }


def test_small():
    for p in (5, 7, 11, 13):
        for size in range(3, p + 1):
            brute = {canonical(s, p) for s in combinations(range(p), size)
                     if all(midpoint_options(s, p))}
            if brute:
                assert brute == set(enumerate_sets(p, size))
                assert not enumerate_sets(p, size - 1)
                break


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prime", type=int, default=79)
    parser.add_argument("--bound", type=int, default=9)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--small-tests", action="store_true")
    args = parser.parse_args()
    p = args.prime
    if p < 3 or any(p % d == 0 for d in range(2, 1 + int(p ** .5))):
        parser.error("--prime must be an odd prime")
    if args.small_tests:
        test_small()
    reps = enumerate_sets(p, args.bound)
    records = [invariants(points, p) for points in reps]
    doc = {"prime": p, "search_bound": args.bound, "minimum": len(reps[0]) if reps else None,
           "orbit_count": len(reps), "set_count": sum(x["orbit_size"] for x in records),
           "orbits": records}
    result = json.dumps(doc, indent=2) + "\n"
    if args.output:
        args.output.write_text(result, encoding="utf-8")
    else:
        print(result, end="")


if __name__ == "__main__":
    main()
