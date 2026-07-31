# margins analysis
"""Test the pre-registered difficulty predictions.

Reads the .stats files emitted by `tpc --stats` (one per slice), aggregates the
population buckets, and reports:

  PREDICTION 1 (load-bearing): star-topped sequences (T_n = K_{1,n-1}) are EASIER than
  average — higher first-try rate, lower mean restarts. If this fails, the difficulty
  metric is measuring the heuristic rather than the instances, and per
  prediction-margins.md the whole line of work stops here.

  PREDICTION 2: sequences with several high-degree non-star trees are over-represented
  among the hardest.

Every sequence in the swept slices is in exactly one bucket, so these are population
statistics, not a sample.

usage: analyze_margins.py --n N --stats 'logs/margins/n10/*.stats' [--trees trees.txt]
"""
import argparse
import glob
import sys
from collections import defaultdict


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--stats", required=True, help="glob of .stats files")
    ap.add_argument("--top", type=int, default=10000, help="how many hardest to profile")
    a = ap.parse_args()

    files = sorted(glob.glob(a.stats))
    if not files:
        sys.exit(f"no stats files matched {a.stats}")

    # buckets[(topstar, nearstars)] = [count, first_try, restarts, gnodes]
    buckets = defaultdict(lambda: [0, 0, 0, 0])
    hard = []
    trees = {}   # (k,t) -> feature dict
    for f in files:
        for line in open(f):
            p = line.split()
            if not p:
                continue
            if p[0] == "BUCKET":
                d = dict(x.split("=") for x in p[1:])
                key = (int(d["topstar"]), int(d["nearstars"]))
                b = buckets[key]
                b[0] += int(d["count"]); b[1] += int(d["first_try"])
                b[2] += int(d["restarts"]); b[3] += int(d["gnodes"])
            elif p[0] == "HARD":
                d = dict(x.split("=") for x in p[1:])
                hard.append((int(d["restarts"]), int(d["gnodes"]), int(d["idx"])))
            elif p[0] == "TREE":
                d = dict(x.split("=") for x in p[1:])
                trees[(int(d["k"]), int(d["t"]))] = {
                    "maxdeg": int(d["maxdeg"]), "leaves": int(d["leaves"]),
                    "diam": int(d["diam"]), "star": int(d["star"]),
                    "nearstar": int(d["nearstar"])}

    tot = sum(b[0] for b in buckets.values())
    print(f"slices={len(files)}  sequences={tot:,}")

    # ---------------- PREDICTION 1 ----------------
    agg = {0: [0, 0, 0, 0], 1: [0, 0, 0, 0]}
    for (ts, _ns), b in buckets.items():
        for i in range(4):
            agg[ts][i] += b[i]

    def line(label, b):
        c, ft, r, g = b
        if c == 0:
            return f"  {label:<28} (empty)"
        return (f"  {label:<28} n={c:>12,}  first-try {100*ft/c:6.2f}%  "
                f"restarts/seq {r/c:7.4f}  greedy-nodes/seq {g/c:9.1f}")

    print("\n=== PREDICTION 1: star-topped sequences should be EASIER ===")
    print(line("T_n IS the star", agg[1]))
    print(line("T_n is not the star", agg[0]))
    print(line("whole population", [agg[0][i] + agg[1][i] for i in range(4)]))

    verdict = None
    if agg[1][0] == 0:
        print("\n  INCONCLUSIVE: no star-topped sequences in this data.")
        verdict = False
    else:
        ft_star = agg[1][1] / agg[1][0]
        ft_pop = (agg[0][1] + agg[1][1]) / tot
        r_star = agg[1][2] / agg[1][0]
        r_pop = (agg[0][2] + agg[1][2]) / tot
        easier = (ft_star > ft_pop) and (r_star < r_pop)
        print(f"\n  first-try: star-topped {100*ft_star:.2f}% vs population {100*ft_pop:.2f}% "
              f"({'HIGHER' if ft_star > ft_pop else 'NOT higher'})")
        print(f"  restarts : star-topped {r_star:.4f} vs population {r_pop:.4f} "
              f"({'LOWER' if r_star < r_pop else 'NOT lower'})")
        if easier:
            print("\n  PREDICTION 1 HELD — the metric tracks structure, not just heuristic noise.")
        else:
            print("\n  PREDICTION 1 FAILED — per prediction-margins.md the difficulty metric is")
            print("  measuring the wrong thing. Stop: skip Stage B and Task 2, report it.")
        verdict = easier

    # ---------------- PREDICTION 2 ----------------
    print("\n=== PREDICTION 2: difficulty vs number of near-star trees (maxdeg >= k/2) ===")
    print("  nearstars   count        share    first-try   restarts/seq")
    by_ns = defaultdict(lambda: [0, 0, 0, 0])
    for (_ts, ns), b in buckets.items():
        for i in range(4):
            by_ns[ns][i] += b[i]
    for ns in sorted(by_ns):
        c, ft, r, _g = by_ns[ns]
        print(f"  {ns:>6}   {c:>12,}  {100*c/tot:7.3f}%   {100*ft/c:7.2f}%   {r/c:9.4f}")

    # ---------------- hardest sequences ----------------
    hard.sort(reverse=True)
    keep = hard[:a.top]
    print(f"\n=== HARDEST {len(keep):,} sequences (of the {len(hard):,} retained per-slice) ===")
    if keep:
        print(f"  restart range {keep[-1][0]}..{keep[0][0]}, "
              f"greedy nodes {min(k[1] for k in keep):,}..{max(k[1] for k in keep):,}")
        # decode features
        A = {2:1,3:1,4:2,5:3,6:6,7:11,8:23,9:47,10:106,11:235,12:551}
        n = a.n
        prof = defaultdict(int)
        topstar_hard = 0
        allpath_hard = 0
        nstar_hist = defaultdict(int)
        for r, g, idx in keep:
            x, sq = idx, {}
            for k in range(2, n + 1):
                sq[k] = x % A[k]; x //= A[k]
            ns = sum(trees[(k, sq[k])]["nearstar"] for k in range(2, n + 1)) if trees else -1
            nstar_hist[ns] += 1
            if trees and trees[(n, sq[n])]["star"]:
                topstar_hard += 1
            if trees and all(trees[(k, sq[k])]["maxdeg"] <= 2 for k in range(4, n + 1)):
                allpath_hard += 1
            if trees:
                prof[tuple(trees[(k, sq[k])]["maxdeg"] for k in range(n, n - 3, -1))] += 1
        print(f"  star-topped among hardest: {topstar_hard} "
              f"({100*topstar_hard/len(keep):.2f}%)")
        print(f"  all-path (maxdeg<=2 for k>=4) among hardest: {allpath_hard}")
        print("  near-star count distribution among hardest:")
        for ns in sorted(nstar_hist):
            print(f"    {ns}: {nstar_hist[ns]} ({100*nstar_hist[ns]/len(keep):.1f}%)")
        print(f"  most common (Delta_n, Delta_n-1, Delta_n-2) among hardest:")
        for p, c in sorted(prof.items(), key=lambda kv: -kv[1])[:8]:
            print(f"    {p}: {c}")

        # leaf and diameter profiles of the largest tree, hardest set vs whole population
        def profile(seqs):
            lf = defaultdict(int); dm = defaultdict(int); md = defaultdict(int)
            for sq in seqs:
                lf[trees[(n, sq[n])]["leaves"]] += 1
                dm[trees[(n, sq[n])]["diam"]] += 1
                md[trees[(n, sq[n])]["maxdeg"]] += 1
            return lf, dm, md

        hard_seqs = []
        for r, g, idx in keep:
            x, sq = idx, {}
            for k in range(2, n + 1):
                sq[k] = x % A[k]; x //= A[k]
            hard_seqs.append(sq)
        hlf, hdm, hmd = profile(hard_seqs)
        # population baseline over T_n alone (uniform over the t(n) trees)
        base = [{n: t} for t in range(A[n])]
        blf, bdm, bmd = profile(base)
        def cmp_table(title, h, b, tot_h, tot_b):
            print(f"  {title}: value  hardest%   population%   ratio")
            for v in sorted(set(h) | set(b)):
                ph = 100 * h.get(v, 0) / tot_h
                pb = 100 * b.get(v, 0) / tot_b
                rat = (ph / pb) if pb else float("inf")
                print(f"    {v:>3}    {ph:8.2f}   {pb:10.2f}   {rat:6.2f}x")
        cmp_table("T_n max degree", hmd, bmd, len(keep), A[n])
        cmp_table("T_n leaves", hlf, blf, len(keep), A[n])
        cmp_table("T_n diameter", hdm, bdm, len(keep), A[n])

    return 0 if verdict else 1


if __name__ == "__main__":
    sys.exit(main())
