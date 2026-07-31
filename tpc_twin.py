# second solver (independent, diff order & heuristics)
import argparse
import os
import random
import subprocess
import sys
import time

A000055 = {2: 1, 3: 1, 4: 2, 5: 3, 6: 6, 7: 11, 8: 23, 9: 47, 10: 106, 11: 235, 12: 551}

def read_trees(path, n):
    out, k = {}, None
    for line in open(path):
        line = line.strip()
        if not line:
            continue
        if line.startswith("#"):
            k = int(line[1:].strip())
            out.setdefault(k, [])
            continue
        out[k].append([int(x) - 1 for x in line.split()[1:]])
    for k in range(2, n + 1):
        if len(out[k]) != A000055[k]:
            sys.exit(f"FATAL: {len(out[k])} trees at k={k}, expected {A000055[k]}")
    return out

def dfs_order(par, k):
    """Return (order, parent_pos) placing tree vertices depth-first from the root.

    order[j] is the tree vertex placed j-th; parent_pos[j] is the position in `order`
    of that vertex's parent (-1 for the root). This is a genuinely different placement
    order from the C engine's, which walks the parent array by index.
    """
    kids = [[] for _ in range(k)]
    for i, p in enumerate(par):
        kids[p].append(i + 1)
    order, ppos, pos_of = [], [], {}
    stack = [(0, -1)]
    while stack:
        v, pp = stack.pop()
        pos_of[v] = len(order)
        order.append(v)
        ppos.append(pp)
        for c in reversed(kids[v]):
            stack.append((c, pos_of[v]))
    assert len(order) == k
    return order, ppos

class Twin:
    def __init__(self, n, trees, rng, use_wlog=True):
        self.n = n
        self.trees = trees
        self.rng = rng
        self.use_wlog = use_wlog
        self.full = (1 << n) - 1
        self.plan = {k: [dfs_order(par, k) for par in trees[k]] for k in range(2, n + 1)}

    def embed(self, adj, k, ti):
        """Find one embedding of trees[k][ti] in residual `adj`; return its edges."""
        order, ppos = self.plan[k][ti]
        n = self.n
        img = [-1] * k
        edges = []
        rng = self.rng

        def rec(j, used):
            if j == k:
                return True
            if j == 0:
                cand = self.full & ~used
            else:
                cand = adj[img[ppos[j]]] & ~used
            if not cand:
                return False
            vs = [v for v in range(n) if (cand >> v) & 1]
            rng.shuffle(vs)
            vs.sort(key=lambda v: bin(adj[v]).count("1"))
            for v in vs:
                img[j] = v
                if j > 0:
                    edges.append((img[ppos[j]], v))
                if rec(j + 1, used | (1 << v)):
                    return True
                if j > 0:
                    edges.pop()
            img[j] = -1
            return False

        if rec(0, 0):
            return list(edges)
        return None

    def attempt(self, seq):
        n = self.n
        adj = [self.full & ~(1 << v) for v in range(n)]
        used_edges = []
        start = n
        if self.use_wlog:
            par = self.trees[n][seq[n]]
            for i, p in enumerate(par):
                u, v = p, i + 1
                adj[u] &= ~(1 << v)
                adj[v] &= ~(1 << u)
                used_edges.append((u, v))
            start = n - 1
        for k in range(start, 1, -1):
            e = self.embed(adj, k, seq[k])
            if e is None:
                return None
            for (u, v) in e:
                adj[u] &= ~(1 << v)
                adj[v] &= ~(1 << u)
            used_edges.extend(e)
        if any(adj):
            return None
        if len(used_edges) != n * (n - 1) // 2:
            return None
        if len({(min(u, v), max(u, v)) for u, v in used_edges}) != len(used_edges):
            return None
        return used_edges

    def pack(self, seq, restarts):
        for r in range(restarts + 1):
            e = self.attempt(seq)
            if e is not None:
                return r
        return None

def escalate_to_sat(n, trees_path, seq, work):
    """Greedy failure is not a result. Hand the sequence to the SAT path, which is a
    complete decision procedure and shares nothing with either search engine.

    Returns True (packs), False (genuinely unsatisfiable — a real event), or None
    (the SAT path itself errored, which is an operational failure, not a verdict).
    """
    arg = ",".join(str(seq[k]) for k in sorted(seq))
    here = os.path.dirname(os.path.abspath(__file__))
    r = subprocess.run(
        [sys.executable, os.path.join(here, "tpc_sat.py"),
         "--n", str(n), "--trees", trees_path, "--seq", arg, "--work", work],
        capture_output=True, text=True)
    if r.returncode == 0 and r.stdout.startswith("SAT "):
        return True
    if r.returncode == 20:
        return False
    print(f"TWIN-ESCALATION-ERROR seq={arg} rc={r.returncode}\n{r.stdout}\n{r.stderr}",
          file=sys.stderr, flush=True)
    return None

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--trees", required=True)
    ap.add_argument("--res", type=int, default=0)
    ap.add_argument("--mod", type=int, default=1)
    ap.add_argument("--seed", type=int, default=19831976)
    ap.add_argument("--no-wlog", action="store_true")
    ap.add_argument("--restarts", type=int, default=200)
    ap.add_argument("--progress", type=int, default=0)
    ap.add_argument("--work", default="/tmp/tpc_twin_sat",
                    help="scratch dir for the SAT escalation path")
    ap.add_argument("--no-escalate", action="store_true",
                    help="report greedy failures instead of escalating (gate diagnostics only)")
    a = ap.parse_args()

    n = a.n
    trees = read_trees(a.trees, n)
    nedge = n * (n - 1) // 2
    if sum(k - 1 for k in range(2, n + 1)) != nedge:
        sys.exit("FATAL: sum(k-1) != C(n,2)")

    rng = random.Random(a.seed + a.res)
    twin = Twin(n, trees, rng, use_wlog=not a.no_wlog)

    ntrees = {k: A000055[k] for k in range(2, n + 1)}
    total = 1
    for k in range(2, n + 1):
        total *= ntrees[k]

    t0 = time.time()
    done = first_try = 0
    escalated = escal_packed = unsat = unresolved = 0
    restart_sum = 0
    for index in range(a.res, total, a.mod):
        x, seq = index, {}
        for k in range(2, n + 1):
            seq[k] = x % ntrees[k]
            x //= ntrees[k]
        r = twin.pack(seq, a.restarts)
        if r is None:
            label = ",".join(str(seq[k]) for k in range(2, n + 1))
            escalated += 1
            print(f"TWIN-ESCALATE index={index} seq={label} (greedy failed "
                  f"{a.restarts} restarts)", file=sys.stderr, flush=True)
            if a.no_escalate:
                unresolved += 1
            else:
                verdict = escalate_to_sat(n, a.trees, seq, a.work)
                if verdict is True:
                    escal_packed += 1
                    print(f"TWIN-ESCALATE-RESOLVED index={index} seq={label} SAT",
                          file=sys.stderr, flush=True)
                elif verdict is False:
                    unsat += 1
                    print(f"TWIN-UNSAT index={index} seq={label} *** SAT path says "
                          f"UNSATISFIABLE ***", file=sys.stderr, flush=True)
                else:
                    unresolved += 1
        else:
            restart_sum += r
            if r == 0:
                first_try += 1
        done += 1
        if a.progress and done % a.progress == 0:
            el = time.time() - t0
            print(f"  twin {done} done, {1000*el/done:.3f} ms/seq, "
                  f"{escalated} escalated, {unsat} unsat, {unresolved} unresolved",
                  file=sys.stderr, flush=True)

    secs = time.time() - t0
    packed = done - unsat - unresolved
    print(f"LEDGER-TWIN n={n} res={a.res} mod={a.mod} seed={a.seed} wlog={0 if a.no_wlog else 1} "
          f"total={done} packed={packed} first_try={first_try} escalated={escalated} "
          f"escalated_packed={escal_packed} UNSAT={unsat} unresolved={unresolved} "
          f"restarts={restart_sum} secs={secs:.2f}")
    if packed + unsat + unresolved != done:
        print("FATAL: twin accounting mismatch", file=sys.stderr)
        return 3
    return 1 if (unsat or unresolved) else 0

if __name__ == "__main__":
    sys.exit(main())
