# naive packing counter
import argparse
import sys
from itertools import product

A000055 = {2: 1, 3: 1, 4: 2, 5: 3, 6: 6, 7: 11, 8: 23, 9: 47, 10: 106, 11: 235}

def read_trees(path, n):
    out = {}
    k = None
    for line in open(path):
        line = line.strip()
        if not line:
            continue
        if line.startswith("#"):
            k = int(line[1:].strip())
            out.setdefault(k, [])
            continue
        vals = [int(x) for x in line.split()]
        out[k].append([v - 1 for v in vals[1:]])
    for k in range(2, n + 1):
        if len(out[k]) != A000055[k]:
            sys.exit(f"FATAL: {len(out[k])} trees at k={k}, expected {A000055[k]}")
    return out

def count_packings(seq_trees, n, wlog=False):
    """seq_trees: list of parent-arrays, largest first. Returns the number of packings.

    With wlog=True the largest tree is nailed to the canonical labeled copy
    {(par[i], i)} and only the rest is searched — the same reduction the C engine
    applies, so the two counts are comparable. (The reduction's validity is checked
    separately, by rerunning the full n=9 sweep with --no-wlog.)
    """
    verts = list(range(n))
    avail = [[u != v for v in range(n)] for u in range(n)]

    start_ti = 0
    if wlog:
        par0 = seq_trees[0]
        for i, p in enumerate(par0):
            u, v = p, i + 1
            avail[u][v] = avail[v][u] = False
        start_ti = 1

    def place(ti):
        if ti == len(seq_trees):
            for u in range(n):
                for v in range(u + 1, n):
                    if avail[u][v]:
                        return 0
            return 1
        par = seq_trees[ti]
        k = len(par) + 1
        img = [-1] * k
        used = [False] * n
        total = 0

        def rec(i):
            nonlocal total
            if i == k:
                for j in range(1, k):
                    u, v = img[par[j - 1]], img[j]
                    avail[u][v] = avail[v][u] = False
                total += place(ti + 1)
                for j in range(1, k):
                    u, v = img[par[j - 1]], img[j]
                    avail[u][v] = avail[v][u] = True
                return
            for v in verts:
                if used[v]:
                    continue
                if i > 0 and not avail[img[par[i - 1]]][v]:
                    continue
                img[i] = v
                used[v] = True
                rec(i + 1)
                used[v] = False
            img[i] = -1

        rec(0)
        return total

    return place(start_ti)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--trees", required=True)
    ap.add_argument("--wlog", action="store_true",
                    help="nail the largest tree to the canonical copy, as the C engine does")
    a = ap.parse_args()
    n = a.n
    trees = read_trees(a.trees, n)

    total = 1
    for k in range(2, n + 1):
        total *= A000055[k]
    for index in range(total):
        x, seq = index, {}
        for k in range(2, n + 1):
            seq[k] = x % A000055[k]
            x //= A000055[k]
        ordered = [trees[k][seq[k]] for k in range(n, 1, -1)]
        c = count_packings(ordered, n, wlog=a.wlog)
        print("COUNT seq=" + ",".join(str(seq[k]) for k in range(2, n + 1)) + f" packings={c}")

if __name__ == "__main__":
    sys.exit(main())
