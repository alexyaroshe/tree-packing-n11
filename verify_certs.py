import argparse
import os
import sys
from collections import defaultdict

A000055 = {2: 1, 3: 1, 4: 2, 5: 3, 6: 6, 7: 11, 8: 23, 9: 47,
           10: 106, 11: 235, 12: 551, 13: 1301, 14: 3159}

def ahu_unrooted(adj, verts):
    """AHU canonical form of an unrooted tree given as an adjacency dict."""
    deg = {v: len(adj[v]) for v in verts}
    remaining = set(verts)
    leaves = [v for v in remaining if deg[v] <= 1]
    while len(remaining) > 2:
        nxt = []
        for v in leaves:
            remaining.discard(v)
            for w in adj[v]:
                if w in remaining:
                    deg[w] -= 1
                    if deg[w] == 1:
                        nxt.append(w)
        leaves = nxt
    centre = sorted(remaining)

    def code(v, parent):
        kids = sorted(code(w, v) for w in adj[v] if w != parent)
        return "(" + "".join(kids) + ")"

    if len(centre) == 1:
        return code(centre[0], None)
    a, b = centre
    return min(code(a, b) + code(b, a), code(b, a) + code(a, b))

def load_reference_trees(path, n):
    """-> {k: [canonical_form, ...]} for the trees named by each sequence index."""
    raw = defaultdict(list)
    k = None
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            if line.startswith("#"):
                k = int(line[1:].strip())
                continue
            vals = [int(x) for x in line.split()]
            raw[k].append([v - 1 for v in vals[1:]])
    forms = {}
    for k in range(2, n + 1):
        if len(raw[k]) != A000055[k]:
            sys.exit(f"FATAL: tree file has {len(raw[k])} trees at k={k}, expected {A000055[k]}")
        fk = []
        for par in raw[k]:
            adj = defaultdict(list)
            for i, p in enumerate(par):
                child = i + 1
                adj[child].append(p)
                adj[p].append(child)
            fk.append(ahu_unrooted(adj, list(range(k))))
        forms[k] = fk
    return forms

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--trees", required=True)
    ap.add_argument("--cert", required=True)
    ap.add_argument("--res", type=int, default=0)
    ap.add_argument("--mod", type=int, default=1)
    ap.add_argument("--unsat", default=None,
                    help="slice's .unsat file; its sequences are expected to have no certificate")
    ap.add_argument("--limit", type=int, default=0, help="verify only the first K certificates")
    ap.add_argument("--explicit", action="store_true",
                    help="probe format: each record is (n-1) LE uint16 tree indices then "
                         "the C(n,2) certificate bytes (sequence order is not implied by "
                         "enumeration, so it is carried in the record)")
    a = ap.parse_args()

    n = a.n
    nedge = n * (n - 1) // 2
    if sum(k - 1 for k in range(2, n + 1)) != nedge:
        sys.exit("FATAL: sum(k-1) != C(n,2)")

    pair = {}
    eid = 0
    for u in range(n):
        for v in range(u + 1, n):
            pair[eid] = (u, v)
            eid += 1
    assert eid == nedge

    ref = load_reference_trees(a.trees, n)
    ntrees = {k: A000055[k] for k in range(2, n + 1)}

    total_seqs = 1
    for k in range(2, n + 1):
        total_seqs *= ntrees[k]
    slice_seqs = len(range(a.res, total_seqs, a.mod))

    n_unsat = 0
    if a.unsat and os.path.exists(a.unsat):
        with open(a.unsat) as f:
            n_unsat = sum(1 for line in f if line.strip())

    block_sizes = [(k, k - 1) for k in range(n, 1, -1)]

    if a.explicit:
        rec = 2 * (n - 1) + nedge
        size_e = os.path.getsize(a.cert)
        if size_e % rec:
            print(f"FAIL: probe file size {size_e} is not a multiple of the record size {rec}")
            return 1
        nrec = size_e // rec
        checked = 0
        with open(a.cert, "rb") as f:
            while True:
                buf = f.read(rec)
                if not buf:
                    break
                if len(buf) < rec:
                    print(f"FAIL: truncated probe record at {checked}")
                    return 1
                seq = {}
                for j, k in enumerate(range(2, n + 1)):
                    seq[k] = buf[2 * j] | (buf[2 * j + 1] << 8)
                    if not (0 <= seq[k] < ntrees[k]):
                        print(f"FAIL: record {checked} names tree {seq[k]} at k={k} "
                              f"(only {ntrees[k]} exist)")
                        return 1
                ids = list(buf[2 * (n - 1):])
                if sorted(ids) != list(range(nedge)):
                    print(f"FAIL E1 record={checked}: not a permutation of 0..{nedge-1}")
                    return 1
                off = 0
                for k, m in block_sizes:
                    block = ids[off:off + m]; off += m
                    adj = defaultdict(list); verts = set()
                    for e in block:
                        u, v = pair[e]
                        adj[u].append(v); adj[v].append(u); verts.add(u); verts.add(v)
                    if len(verts) != k or len(block) != k - 1:
                        print(f"FAIL E3 record={checked} k={k}")
                        return 1
                    start = next(iter(verts)); seen = {start}; stack = [start]
                    while stack:
                        x2 = stack.pop()
                        for w in adj[x2]:
                            if w not in seen:
                                seen.add(w); stack.append(w)
                    if len(seen) != k:
                        print(f"FAIL E4 record={checked} k={k}: disconnected")
                        return 1
                    if ahu_unrooted(adj, sorted(verts)) != ref[k][seq[k]]:
                        print(f"FAIL E5 record={checked} k={k}: not isomorphic to tree #{seq[k]}")
                        return 1
                checked += 1
        print(f"VERIFIED-PROBE n={n}: {checked} certificates, all of E1-E5 hold")
        return 0

    size = os.path.getsize(a.cert)
    expected = (slice_seqs - n_unsat) * nedge
    if size % nedge:
        print(f"FAIL E6: cert file size {size} is not a multiple of {nedge}")
        return 1
    n_certs = size // nedge
    if not a.limit and size != expected:
        print(f"FAIL E6: cert file holds {n_certs} certificates, slice has {slice_seqs} "
              f"sequences and {n_unsat} unsat -> expected {slice_seqs - n_unsat}")
        return 1

    checked = 0
    with open(a.cert, "rb") as f:
        for j, index in enumerate(range(a.res, total_seqs, a.mod)):
            if a.limit and checked >= a.limit:
                break
            buf = f.read(nedge)
            if len(buf) < nedge:
                print(f"FAIL E6: certificate stream ended at sequence {j} (index {index})")
                return 1

            x = index
            seq = {}
            for k in range(2, n + 1):
                seq[k] = x % ntrees[k]
                x //= ntrees[k]

            ids = list(buf)
            if sorted(ids) != list(range(nedge)):
                print(f"FAIL E1 index={index}: edge ids are not a permutation of 0..{nedge-1}")
                return 1

            off = 0
            for k, m in block_sizes:
                block = ids[off:off + m]
                off += m
                adj = defaultdict(list)
                verts = set()
                for e in block:
                    u, v = pair[e]
                    adj[u].append(v)
                    adj[v].append(u)
                    verts.add(u)
                    verts.add(v)
                if len(verts) != k or len(block) != k - 1:
                    print(f"FAIL E3 index={index} k={k}: {len(verts)} vertices, {len(block)} edges")
                    return 1
                start = next(iter(verts))
                seen = {start}
                stack = [start]
                while stack:
                    v = stack.pop()
                    for w in adj[v]:
                        if w not in seen:
                            seen.add(w)
                            stack.append(w)
                if len(seen) != k:
                    print(f"FAIL E4 index={index} k={k}: image is disconnected")
                    return 1
                if ahu_unrooted(adj, sorted(verts)) != ref[k][seq[k]]:
                    print(f"FAIL E5 index={index} k={k}: image is not isomorphic to tree #{seq[k]}")
                    return 1
            checked += 1

    print(f"VERIFIED n={n} slice={a.res}/{a.mod}: {checked} certificates, "
          f"{n_unsat} unsat, all of E1-E6 hold")
    return 0

if __name__ == "__main__":
    sys.exit(main())
