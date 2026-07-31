// solver
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 14
#define MAXK MAXN
#define MAXTREES 4096    
#define GREEDY_RESTARTS 200

typedef struct { int k; unsigned char par[MAXK]; } Tree;

static int      N;                       
static Tree     trees[MAXN + 1][MAXTREES];
static int      ntrees[MAXN + 1];
static int      edge_id[MAXN][MAXN];     
static int      NEDGE;
static int      use_wlog = 1;
static int      force_exact = 0;         
static int      count_mode = 0;          
static int      drop_edge = -1;          
static unsigned long long pack_count;    

static uint16_t adj[MAXN];
static uint16_t FULLMASK;

static int seq[MAXN + 1];

static unsigned char cert[MAXN * MAXN];
static int cert_len;

static unsigned long long c_total = 0;      
static unsigned long long c_stageA = 0;     
static unsigned long long c_stageA_r0 = 0;  
static unsigned long long c_escalated = 0;  
static unsigned long long c_stageB = 0;     
static unsigned long long c_unsat = 0;      
static unsigned long long c_restarts = 0;   
static unsigned long long c_nodes = 0;      

static int  stats_mode = 0;
static const char *stats_path = NULL;

static int probe_mode = 0;                  
static long long probe_count = 0;
static long long probe_drawn = 0, probe_kept = 0;
static const char *probe_cert_path = NULL;
static FILE *fprobe = NULL;
static unsigned long long g_nodes;          

static int t_maxdeg[MAXN + 1][MAXTREES];
static int t_leaves[MAXN + 1][MAXTREES];
static int t_diam[MAXN + 1][MAXTREES];
static int t_isstar[MAXN + 1][MAXTREES];
static int t_nearstar[MAXN + 1][MAXTREES];  

static unsigned long long b_cnt[2][MAXN + 2], b_first[2][MAXN + 2];
static unsigned long long b_rest[2][MAXN + 2], b_nodes[2][MAXN + 2];

#define TOPK 256
static struct { long long idx; unsigned r; unsigned long long nodes; } topk[TOPK];
static int topk_n = 0;

static uint64_t rng_state;
static inline uint64_t rnd64(void) {
    uint64_t x = rng_state;
    x ^= x << 13; x ^= x >> 7; x ^= x << 17;
    return rng_state = x;
}
static inline int rnd_below(int m) { return (int)(rnd64() % (uint64_t)m); }

static void load_trees(const char *path) {
    FILE *f = fopen(path, "r");
    if (!f) { fprintf(stderr, "FATAL: cannot open tree file %s\n", path); exit(2); }
    char line[512];
    int cur_k = 0;
    while (fgets(line, sizeof line, f)) {
        if (line[0] == '#') {                      
            if (sscanf(line, "# %d", &cur_k) != 1) { fprintf(stderr, "FATAL: bad header %s", line); exit(2); }
            if (cur_k < 1 || cur_k > MAXN) { fprintf(stderr, "FATAL: k=%d out of range\n", cur_k); exit(2); }
            continue;
        }
        if (line[0] == '\n' || line[0] == '\0') continue;
        if (cur_k == 0) { fprintf(stderr, "FATAL: tree data before any header\n"); exit(2); }
        int vals[MAXK], cnt = 0;
        char *p = line;
        while (cnt < MAXK) {
            char *end;
            long v = strtol(p, &end, 10);
            if (end == p) break;
            vals[cnt++] = (int)v; p = end;
        }
        if (cnt != cur_k) { fprintf(stderr, "FATAL: k=%d line has %d entries\n", cur_k, cnt); exit(2); }
        if (vals[0] != 0)  { fprintf(stderr, "FATAL: k=%d root parent is %d not 0\n", cur_k, vals[0]); exit(2); }
        if (ntrees[cur_k] >= MAXTREES) { fprintf(stderr, "FATAL: too many trees at k=%d\n", cur_k); exit(2); }
        Tree *t = &trees[cur_k][ntrees[cur_k]++];
        t->k = cur_k;
        t->par[0] = 0;
        for (int i = 1; i < cur_k; i++) {
            int par0 = vals[i] - 1;                
            if (par0 < 0 || par0 >= i) {
                fprintf(stderr, "FATAL: k=%d vertex %d parent %d not < %d\n", cur_k, i, par0, i);
                exit(2);
            }
            t->par[i] = (unsigned char)par0;
        }
    }
    fclose(f);
}

static void compute_tree_features(void) {
    for (int k = 2; k <= MAXN; k++) {
        for (int t = 0; t < ntrees[k]; t++) {
            const Tree *T = &trees[k][t];
            int deg[MAXK]; for (int i = 0; i < k; i++) deg[i] = 0;
            for (int i = 1; i < k; i++) { deg[i]++; deg[T->par[i]]++; }
            int md = 0, lv = 0;
            for (int i = 0; i < k; i++) { if (deg[i] > md) md = deg[i]; if (deg[i] == 1) lv++; }
            t_maxdeg[k][t] = md;
            t_leaves[k][t] = lv;
            t_isstar[k][t] = (md == k - 1);
            t_nearstar[k][t] = (2 * md >= k);
            
            int adjl[MAXK][MAXK], adjn[MAXK];
            for (int i = 0; i < k; i++) adjn[i] = 0;
            for (int i = 1; i < k; i++) {
                int p = T->par[i];
                adjl[i][adjn[i]++] = p; adjl[p][adjn[p]++] = i;
            }
            int dist[MAXK], q[MAXK];
            int far = 0, diam = 0;
            for (int pass = 0; pass < 2; pass++) {
                int src = (pass == 0) ? 0 : far;
                for (int i = 0; i < k; i++) dist[i] = -1;
                int head = 0, tail = 0; q[tail++] = src; dist[src] = 0; far = src;
                while (head < tail) {
                    int v = q[head++];
                    if (dist[v] > dist[far]) far = v;
                    for (int a = 0; a < adjn[v]; a++) {
                        int w = adjl[v][a];
                        if (dist[w] < 0) { dist[w] = dist[v] + 1; q[tail++] = w; }
                    }
                }
                diam = dist[far];
            }
            t_diam[k][t] = diam;
        }
    }
}

static void stats_record(long long idx, int restarts, int solved) {
    int nstar = 0;
    for (int k = 2; k <= N; k++) if (t_nearstar[k][seq[k]]) nstar++;
    int topstar = t_isstar[N][seq[N]] ? 1 : 0;
    b_cnt[topstar][nstar]++;
    if (solved && restarts == 0) b_first[topstar][nstar]++;
    b_rest[topstar][nstar] += (unsigned long long)restarts;
    b_nodes[topstar][nstar] += g_nodes;
    
    if (topk_n < TOPK) {
        topk[topk_n].idx = idx; topk[topk_n].r = (unsigned)restarts; topk[topk_n].nodes = g_nodes;
        topk_n++;
    } else {
        int worst = 0;
        for (int i = 1; i < TOPK; i++)
            if (topk[i].r < topk[worst].r ||
                (topk[i].r == topk[worst].r && topk[i].nodes < topk[worst].nodes)) worst = i;
        if ((unsigned)restarts > topk[worst].r ||
            ((unsigned)restarts == topk[worst].r && g_nodes > topk[worst].nodes)) {
            topk[worst].idx = idx; topk[worst].r = (unsigned)restarts; topk[worst].nodes = g_nodes;
        }
    }
}

static const int A000055[] = {0,1,1,1,2,3,6,11,23,47,106,235,551,1301,3159};
static void check_tree_counts(void) {
    for (int k = 2; k <= N; k++) {
        if (ntrees[k] != A000055[k]) {
            fprintf(stderr, "FATAL: k=%d has %d trees, A000055 says %d\n", k, ntrees[k], A000055[k]);
            exit(2);
        }
    }
}

static int      emb_k;
static const unsigned char *emb_par;
static int      emb_img[MAXK];
static uint16_t emb_used;
static int      emb_edges[MAXK];        

static int embed_one(int i) {
    if (i == emb_k) return 1;
    g_nodes++;
    uint16_t cand = (i == 0) ? (uint16_t)(FULLMASK & ~emb_used)
                             : (uint16_t)(adj[emb_img[emb_par[i]]] & ~emb_used);
    if (!cand) return 0;
    int vs[MAXN], nv = 0;
    for (int v = 0; v < N; v++) if (cand & (1u << v)) vs[nv++] = v;
    for (int a = nv - 1; a > 0; a--) { int b = rnd_below(a + 1), t = vs[a]; vs[a] = vs[b]; vs[b] = t; }
    for (int a = 0; a < nv; a++) {
        int v = vs[a];
        emb_img[i] = v;
        emb_used |= (uint16_t)(1u << v);
        if (i > 0) emb_edges[i - 1] = edge_id[emb_img[emb_par[i]]][v];
        if (embed_one(i + 1)) return 1;
        emb_used &= (uint16_t)~(1u << v);
    }
    return 0;
}

static void remove_embedding(void) {
    for (int i = 1; i < emb_k; i++) {
        int u = emb_img[emb_par[i]], v = emb_img[i];
        adj[u] &= (uint16_t)~(1u << v);
        adj[v] &= (uint16_t)~(1u << u);
    }
}
static void restore_embedding(int img[], const unsigned char *par, int k) {
    for (int i = 1; i < k; i++) {
        int u = img[par[i]], v = img[i];
        adj[u] |= (uint16_t)(1u << v);
        adj[v] |= (uint16_t)(1u << u);
    }
}

static int drop_u, drop_v;
static void init_residual(void) {
    for (int v = 0; v < N; v++) adj[v] = (uint16_t)(FULLMASK & ~(1u << v));
    if (drop_edge >= 0) {
        adj[drop_u] &= (uint16_t)~(1u << drop_v);
        adj[drop_v] &= (uint16_t)~(1u << drop_u);
    }
}

static void place_wlog_top(const Tree *t) {
    for (int i = 1; i < t->k; i++) {
        int u = t->par[i], v = i;
        adj[u] &= (uint16_t)~(1u << v);
        adj[v] &= (uint16_t)~(1u << u);
        cert[cert_len++] = (unsigned char)edge_id[u][v];
    }
}

static int greedy_attempt(void) {
    init_residual();
    cert_len = 0;
    int start = N;
    if (use_wlog) { place_wlog_top(&trees[N][seq[N]]); start = N - 1; }
    for (int k = start; k >= 2; k--) {
        const Tree *t = &trees[k][seq[k]];
        emb_k = t->k; emb_par = t->par; emb_used = 0;
        if (!embed_one(0)) return 0;
        remove_embedding();
        for (int i = 0; i < emb_k - 1; i++) cert[cert_len++] = (unsigned char)emb_edges[i];
    }
    return 1;
}

static int  ex_img[MAXN + 1][MAXK];     
static int  ex_edges[MAXN + 1][MAXK];

static int solve_exact(int level);

static int exact_embed(int level, int i, uint16_t used) {
    const Tree *t = &trees[level][seq[level]];
    if (i == t->k) {
        for (int j = 1; j < t->k; j++) {
            int u = ex_img[level][t->par[j]], v = ex_img[level][j];
            adj[u] &= (uint16_t)~(1u << v);
            adj[v] &= (uint16_t)~(1u << u);
        }
        int ok = solve_exact(level - 1);
        if (!ok) restore_embedding(ex_img[level], t->par, t->k);
        return ok;
    }
    uint16_t cand = (i == 0) ? (uint16_t)(FULLMASK & ~used)
                             : (uint16_t)(adj[ex_img[level][t->par[i]]] & ~used);
    for (int v = 0; v < N; v++) {
        if (!(cand & (1u << v))) continue;
        c_nodes++;
        ex_img[level][i] = v;
        if (i > 0) ex_edges[level][i - 1] = edge_id[ex_img[level][t->par[i]]][v];
        if (exact_embed(level, i + 1, (uint16_t)(used | (1u << v)))) return 1;
    }
    return 0;
}

static int solve_exact(int level) {
    if (level == 1) {                    
        for (int v = 0; v < N; v++) if (adj[v]) return 0;
        if (count_mode) { pack_count++; return 0; }   
        return 1;
    }
    return exact_embed(level, 0, 0);
}

static int run_exact(void) {
    init_residual();
    cert_len = 0;
    int start = N;
    if (use_wlog) { place_wlog_top(&trees[N][seq[N]]); start = N - 1; }
    int wlog_edges = cert_len;                 
    if (!solve_exact(start)) return 0;
    cert_len = wlog_edges;                     
    for (int k = start; k >= 2; k--) {
        const Tree *t = &trees[k][seq[k]];
        for (int j = 1; j < t->k; j++)
            cert[cert_len++] = (unsigned char)edge_id[ex_img[k][t->par[j]]][ex_img[k][j]];
    }
    return 1;
}

static FILE *fcert = NULL, *funsat = NULL;

static void describe_sequence(char *buf, size_t sz) {
    size_t o = 0;
    for (int k = 2; k <= N; k++) o += snprintf(buf + o, sz - o, "%s%d", k == 2 ? "" : ",", seq[k]);
}

static void handle_sequence(long long idx) {
    c_total++;
    g_nodes = 0;
    if (count_mode) {                      
        pack_count = 0;
        run_exact();                       
        char buf[256]; describe_sequence(buf, sizeof buf);
        printf("COUNT seq=%s packings=%llu\n", buf, pack_count);
        if (pack_count) c_stageA++; else { c_unsat++; }
        return;
    }
    int solved = 0, restarts = 0;
    if (!force_exact) {
        for (restarts = 0; restarts <= GREEDY_RESTARTS; restarts++) {
            if (greedy_attempt()) { solved = 1; break; }
        }
        if (stats_mode) stats_record(idx, restarts, solved);
    } else {
        restarts = GREEDY_RESTARTS + 1;    
    }
    if (solved) {
        c_stageA++; c_restarts += (unsigned long long)restarts;
        if (restarts == 0) c_stageA_r0++;
    } else {
        
        c_escalated++;
        if (run_exact()) {
            c_stageB++;
        } else {
            c_unsat++;
            char buf[256]; describe_sequence(buf, sizeof buf);
            fprintf(stderr, "STAGE-B-UNSAT seq=%s\n", buf);
            if (funsat) { fprintf(funsat, "%s\n", buf); fflush(funsat); }
            return;                       
        }
    }
    if (cert_len != NEDGE) {
        char buf[256]; describe_sequence(buf, sizeof buf);
        fprintf(stderr, "FATAL: cert_len=%d != %d for seq=%s\n", cert_len, NEDGE, buf);
        exit(3);
    }
    if (fcert) fwrite(cert, 1, (size_t)NEDGE, fcert);
}

static int probe_accept(void) {
    if (probe_mode == 3) return 1;
    if (probe_mode == 1) {
        
        int c = 0, lo = N - 4; if (lo < 2) lo = 2;
        for (int k = N; k >= lo; k--)
            if (t_nearstar[k][seq[k]] && !t_isstar[k][seq[k]]) c++;
        return c >= 3;
    }
    if (probe_mode == 2) {
        for (int k = N; k > N - 3 && k >= 2; k--)
            if (t_maxdeg[k][seq[k]] > 4) return 0;
        return 1;
    }
    return 0;
}

static void probe_run(void) {
    
    long long cap = probe_count * 10000LL + 100000LL;
    while (probe_kept < probe_count) {
        if (probe_drawn > cap) {
            fprintf(stderr, "FATAL: probe filter accepted %lld of %lld draws; "
                            "it is too rare (or unsatisfiable) at n=%d\n",
                    probe_kept, probe_drawn, N);
            exit(4);
        }
        for (int k = 2; k <= N; k++) seq[k] = rnd_below(ntrees[k]);
        probe_drawn++;
        if (!probe_accept()) continue;
        probe_kept++;
        handle_sequence(-1);
        if (fprobe && cert_len == NEDGE) {
            unsigned char hdr[2 * MAXN];
            int h = 0;
            for (int k = 2; k <= N; k++) {
                hdr[h++] = (unsigned char)(seq[k] & 0xff);
                hdr[h++] = (unsigned char)((seq[k] >> 8) & 0xff);
            }
            fwrite(hdr, 1, (size_t)h, fprobe);
            fwrite(cert, 1, (size_t)NEDGE, fprobe);
        }
    }
}

static void sweep(long long res, long long mod) {
    long long total = 1;
    for (int k = 2; k <= N; k++) total *= ntrees[k];
    for (long long idx = res; idx < total; idx += mod) {
        long long x = idx;
        for (int k = 2; k <= N; k++) { seq[k] = (int)(x % ntrees[k]); x /= ntrees[k]; }
        handle_sequence(idx);
    }
}

int main(int argc, char **argv) {
    const char *treefile = "trees.txt", *certpath = NULL, *unsatpath = NULL;
    long long res = 0, mod = 1;
    uint64_t seed = 20260730ULL;
    N = 0;
    for (int i = 1; i < argc; i++) {
        if      (!strcmp(argv[i], "--n"))       N = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--trees"))   treefile = argv[++i];
        else if (!strcmp(argv[i], "--cert"))    certpath = argv[++i];
        else if (!strcmp(argv[i], "--unsat"))   unsatpath = argv[++i];
        else if (!strcmp(argv[i], "--res"))     res = atoll(argv[++i]);
        else if (!strcmp(argv[i], "--mod"))     mod = atoll(argv[++i]);
        else if (!strcmp(argv[i], "--seed"))    seed = strtoull(argv[++i], NULL, 10);
        else if (!strcmp(argv[i], "--no-wlog")) use_wlog = 0;
        else if (!strcmp(argv[i], "--force-exact")) force_exact = 1;
        else if (!strcmp(argv[i], "--count")) { count_mode = 1; force_exact = 1; }
        else if (!strcmp(argv[i], "--drop-edge")) drop_edge = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--stats")) { stats_mode = 1; stats_path = argv[++i]; }
        else if (!strcmp(argv[i], "--probe")) {
            const char *m = argv[++i];
            if      (!strcmp(m, "danger")) probe_mode = 1;
            else if (!strcmp(m, "hard"))   probe_mode = 2;
            else if (!strcmp(m, "random")) probe_mode = 3;
            else { fprintf(stderr, "FATAL: --probe must be danger|hard|random\n"); return 2; }
        }
        else if (!strcmp(argv[i], "--probe-count")) probe_count = atoll(argv[++i]);
        else if (!strcmp(argv[i], "--probe-cert"))  probe_cert_path = argv[++i];
        else { fprintf(stderr, "unknown arg %s\n", argv[i]); return 2; }
    }
    if (N < 2 || N > MAXN) { fprintf(stderr, "usage: tpc --n N [--trees f] [--cert f] [--unsat f] [--res r --mod m]\n"
        "            [--seed s] [--no-wlog] [--force-exact] [--count] [--drop-edge E]\n"); return 2; }
    rng_state = seed ? seed : 1;

    load_trees(treefile);
    check_tree_counts();
    compute_tree_features();

    NEDGE = 0;
    for (int u = 0; u < N; u++) for (int v = u + 1; v < N; v++) { edge_id[u][v] = edge_id[v][u] = NEDGE++; }
    if (NEDGE != N * (N - 1) / 2) { fprintf(stderr, "FATAL: edge count\n"); return 3; }
    
    int sum = 0; for (int k = 2; k <= N; k++) sum += k - 1;
    if (sum != NEDGE) { fprintf(stderr, "FATAL: sum(k-1)=%d != C(n,2)=%d\n", sum, NEDGE); return 3; }
    FULLMASK = (uint16_t)((1u << N) - 1);

    if (drop_edge >= 0) {
        
        if (drop_edge >= NEDGE) { fprintf(stderr, "FATAL: --drop-edge %d out of range\n", drop_edge); return 2; }
        if (use_wlog) { fprintf(stderr, "FATAL: --drop-edge requires --no-wlog (host is not K_n)\n"); return 2; }
        for (int u = 0; u < N; u++) for (int v = u + 1; v < N; v++)
            if (edge_id[u][v] == drop_edge) { drop_u = u; drop_v = v; }
        fprintf(stderr, "CONTROL: edge %d = {%d,%d} removed from K_%d; every sequence must be UNSAT\n",
                drop_edge, drop_u, drop_v, N);
    }

    if (certpath)  { fcert  = fopen(certpath, "wb"); if (!fcert)  { perror("cert");  return 2; } }
    if (unsatpath) { funsat = fopen(unsatpath, "w"); if (!funsat) { perror("unsat"); return 2; } }

    long long total = 1;
    for (int k = 2; k <= N; k++) total *= ntrees[k];
    fprintf(stderr, "tpc: n=%d trees/size:", N);
    for (int k = 2; k <= N; k++) fprintf(stderr, " %d", ntrees[k]);
    fprintf(stderr, "  total_sequences=%lld  edges=%d  wlog=%d  slice=%lld/%lld  seed=%llu\n",
            total, NEDGE, use_wlog, res, mod, (unsigned long long)seed);

    if (probe_mode && probe_cert_path) {
        fprobe = fopen(probe_cert_path, "wb");
        if (!fprobe) { perror("probe-cert"); return 2; }
    }

    clock_t t0 = clock();
    if (probe_mode) {
        if (probe_count <= 0) { fprintf(stderr, "FATAL: --probe needs --probe-count\n"); return 2; }
        probe_run();
    } else {
        sweep(res, mod);
    }
    double secs = (double)(clock() - t0) / CLOCKS_PER_SEC;
    if (fprobe) fclose(fprobe);

    if (fcert)  fclose(fcert);
    if (funsat) fclose(funsat);

    if (stats_mode && stats_path) {
        FILE *fs = fopen(stats_path, "w");
        if (!fs) { perror("stats"); return 2; }
        fprintf(fs, "# n=%d res=%lld mod=%lld seed=%llu\n", N, res, mod, (unsigned long long)seed);
        
        for (int ts = 0; ts < 2; ts++)
            for (int ns = 0; ns <= N; ns++)
                if (b_cnt[ts][ns])
                    fprintf(fs, "BUCKET topstar=%d nearstars=%d count=%llu first_try=%llu "
                                "restarts=%llu gnodes=%llu\n",
                            ts, ns, b_cnt[ts][ns], b_first[ts][ns], b_rest[ts][ns], b_nodes[ts][ns]);
        for (int i = 0; i < topk_n; i++)
            fprintf(fs, "HARD idx=%lld restarts=%u gnodes=%llu\n",
                    topk[i].idx, topk[i].r, topk[i].nodes);
        
        for (int k = 2; k <= N; k++)
            for (int t = 0; t < ntrees[k]; t++)
                fprintf(fs, "TREE k=%d t=%d maxdeg=%d leaves=%d diam=%d star=%d nearstar=%d\n",
                        k, t, t_maxdeg[k][t], t_leaves[k][t], t_diam[k][t],
                        t_isstar[k][t], t_nearstar[k][t]);
        fclose(fs);
    }

    if (probe_mode) {
        printf("PROBE n=%d mode=%s drawn=%lld kept=%lld acceptance=%.9f seed=%llu "
               "packed=%llu escalated=%llu stageB=%llu UNSAT=%llu restarts=%llu secs=%.2f\n",
               N, probe_mode == 1 ? "danger" : probe_mode == 2 ? "hard" : "random",
               probe_drawn, probe_kept, probe_drawn ? (double)probe_kept / (double)probe_drawn : 0.0,
               (unsigned long long)seed, c_stageA + c_stageB, c_escalated, c_stageB, c_unsat,
               c_restarts, secs);
    }
    
    printf("LEDGER n=%d res=%lld mod=%lld seed=%llu wlog=%d total=%llu stageA=%llu stageA_first_try=%llu "
           "escalated=%llu stageB=%llu UNSAT=%llu greedy_restarts=%llu exact_nodes=%llu secs=%.2f\n",
           N, res, mod, (unsigned long long)seed, use_wlog, c_total, c_stageA, c_stageA_r0,
           c_escalated, c_stageB, c_unsat, c_restarts, c_nodes, secs);

    if (c_stageA + c_stageB + c_unsat != c_total) {
        fprintf(stderr, "FATAL: accounting mismatch %llu+%llu+%llu != %llu\n",
                c_stageA, c_stageB, c_unsat, c_total);
        return 3;
    }
    return c_unsat ? 1 : 0;
}
