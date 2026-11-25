"""Exhaustive labelled simple graphs up to six vertices, using only Python's standard library."""

from itertools import combinations


def slater(adj):
    covered = 0
    for k, degree in enumerate(sorted((m.bit_count() for m in adj), reverse=True), 1):
        covered += degree + 1
        if covered >= len(adj):
            return k
    return 0


def smallest_maximal(adj):
    """Enumerate every matching once, rejecting non-independent unmatched sets."""
    n = len(adj)
    best = n

    def search(free, unmatched, size):
        nonlocal best
        if size >= best:
            return
        if free == 0:
            best = size
            return
        vbit = free & -free
        v = vbit.bit_length() - 1
        rest = free ^ vbit
        if not (adj[v] & unmatched):
            search(rest, unmatched | vbit, size)
        candidates = adj[v] & rest
        while candidates:
            wbit = candidates & -candidates
            search(rest ^ wbit, unmatched, size + 1)
            candidates ^= wbit

    search((1 << n) - 1, 0, 0)
    return best


def run():
    total = 0
    for n in range(2, 7):
        edges = list(combinations(range(n), 2))
        tested = tight = 0
        for mask in range(1 << len(edges)):
            adj = [0] * n
            for bit, (a, b) in enumerate(edges):
                if (mask >> bit) & 1:
                    adj[a] |= 1 << b
                    adj[b] |= 1 << a
            if min(v.bit_count() for v in adj) < 2:
                continue
            sl, mm = slater(adj), smallest_maximal(adj)
            if sl > mm:
                raise ValueError((n, mask, sl, mm))
            tested += 1
            tight += sl == mm
        total += tested
        print(f'n={n}: checked {tested}, equality {tight}')
    path4 = [0b0010, 0b0101, 0b1010, 0b0100]
    pair = slater(path4), smallest_maximal(path4)
    if pair != (2, 1):
        raise ValueError(('path4', pair))
    print(f'Total graphs of minimum degree at least two: {total}')
    print('P4 (minimum degree one): Slater=2, minimum maximal matching=1')


if __name__ == '__main__':
    run()
