/* Local search for balanced r-colourings of K_n, r=6 (7-subsets must see all 6 colours).
 *
 * Fork of tools/locsearch.c (r=5). Same algorithm and incremental-scoring machinery;
 * only the r-dependent parts change: R=6, (R+1)=7 nested enumeration loops,
 * EPS=C(7,2)=21 edges per subset, and the large per-subset arrays are malloc'd to the
 * actual NS=C(n,7) so smaller n stays light (n can reach 37/38, where NS ~ 10-13M).
 *
 * Minimizes the number of 7-subsets missing at least one colour, by focused random walk:
 * pick a random violated subset, pick a random missing colour c, recolour a random edge
 * inside the subset to c (greedy tie-broken by delta, with noise). Incremental scoring via
 * per-subset colour counts (set_colour/delta are already R-agnostic).
 *
 * verify.py remains the referee: on reaching 0 violations this program prints the colouring
 * as JSON to stdout and exits 0; caller MUST run verify.py on it.
 *
 * Build:  cc -O3 -o tools/locsearch6 tools/locsearch6.c
 * Usage:  ./tools/locsearch6 N SEED MAXSTEPS [INIT.json [NOISE_PCT [BESTOUT [GREEDYK]]]]
 *         INIT.json optional warm start (verify.py format, n=N); "-" = random.
 *         NOISE_PCT: random-edge probability in percent (default 20).
 *         BESTOUT: file to write best-seen colouring as JSON (periodically + on exit).
 *         GREEDYK: on a greedy step, evaluate delta for this many of the subset's 21 edges
 *                  and take the best (default 4; 0 = all 21). Each delta scans edeg=C(n-2,5)
 *                  subsets, which at n=36 (edeg=278k, cnt array 50MB > cache) is the dominant
 *                  cost, so a small sample buys most of the guidance for a fraction of the work.
 *         Progress to stderr; JSON to stdout only on success (0 violations).
 *         MAXSTEPS=0 => just score the init and dump it to BESTOUT (validation mode).
 *         Stagnation policy: restore best state after 400k non-improving steps.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define R 6
#define NMAX 38
#define EPS (( (R+1)*R )/2)            /* edges per (R+1)-subset = C(7,2) = 21 */
#define EMAX (NMAX*(NMAX-1)/2)
#define ENDGAME 3000                   /* below this many violations, switch to full greedy + low noise */

static int N, E;                       /* vertices, edges */
static long NS;                        /* number of (R+1)-subsets = C(N,7) */
static int eid[NMAX][NMAX];            /* edge id */
static int col[EMAX];                  /* current colouring */
static uint8_t (*cnt)[R];              /* per-subset colour counts   [NS][R]  */
static uint8_t *nmiss;                 /* # colours with count 0     [NS]     */
static int16_t (*sedges)[EPS];         /* edge ids of each subset     [NS][21] */
static int32_t *esets[EMAX];           /* subsets containing edge e */
static long edeg;                      /* = C(N-2, R-1) subsets per edge */
static int *vlist, nviol;              /* violated subset ids, swap-remove */
static int *vpos;                      /* position of subset in vlist, -1 if absent */

static uint64_t rng;
static inline uint64_t rnd(void){ rng ^= rng<<13; rng ^= rng>>7; rng ^= rng<<17; return rng; }

static long nCk(int n, int k){
    if (k < 0 || k > n) return 0;
    long r = 1;
    for (int i = 0; i < k; i++) r = r * (n - i) / (i + 1);   /* exact: r = C(n,i+1) each step */
    return r;
}

static void viol_add(int s){ if (vpos[s] < 0){ vpos[s] = nviol; vlist[nviol++] = s; } }
static void viol_del(int s){ int p = vpos[s]; if (p >= 0){ int t = vlist[--nviol]; vlist[p] = t; vpos[t] = p; vpos[s] = -1; } }

/* recolour edge e to c, updating all structures */
static void set_colour(int e, int c){
    int old = col[e];
    if (old == c) return;
    col[e] = c;
    int32_t *ss = esets[e];
    for (long k = 0; k < edeg; k++){
        int s = ss[k];
        uint8_t *q = cnt[s];
        if (--q[old] == 0) if (++nmiss[s] == 1) viol_add(s);
        if (q[c]++ == 0) if (--nmiss[s] == 0) viol_del(s);
    }
}

/* delta in #violations if edge e -> colour c (no state change) */
static int delta(int e, int c){
    int old = col[e], d = 0;
    if (old == c) return 0;
    int32_t *ss = esets[e];
    for (long k = 0; k < edeg; k++){
        int s = ss[k];
        uint8_t *q = cnt[s];
        int m = nmiss[s];
        int m2 = m + (q[old] == 1) - (q[c] == 0);
        d += (m2 > 0) - (m > 0);
    }
    return d;
}

static void write_json(FILE *f){
    fprintf(f, "{\"r\": %d, \"n\": %d, \"colours\": [", R, N);
    for (int i = 0; i < N; i++){
        fprintf(f, "[");
        for (int j = 0; j < N; j++) fprintf(f, "%d%s", i==j ? -1 : col[eid[i][j]], j<N-1 ? ", " : "");
        fprintf(f, "]%s", i<N-1 ? ", " : "");
    }
    fprintf(f, "]}\n");
}

int main(int argc, char **argv){
    if (argc < 4){ fprintf(stderr, "usage: %s N SEED MAXSTEPS [INIT.json [NOISE_PCT [BESTOUT]]]\n", argv[0]); return 2; }
    N = atoi(argv[1]);
    if (N < R+1 || N > NMAX){ fprintf(stderr, "N must be in %d..%d\n", R+1, NMAX); return 2; }
    rng = strtoull(argv[2], 0, 10) * 2654435761u + 1; for (int i = 0; i < 10; i++) rnd();
    long long maxsteps = atoll(argv[3]);
    int noise = (argc >= 6) ? atoi(argv[5]) : 20;
    const char *bestout = (argc >= 7) ? argv[6] : 0;
    int greedyk = (argc >= 8) ? atoi(argv[7]) : 4;
    if (greedyk <= 0 || greedyk > EPS) greedyk = EPS;

    E = 0;
    for (int i = 0; i < N; i++) for (int j = i+1; j < N; j++){ eid[i][j] = eid[j][i] = E++; }

    NS = nCk(N, R+1);
    edeg = nCk(N-2, R-1);
    /* allocate per-subset structures sized to the actual n */
    cnt    = malloc((size_t)NS * sizeof *cnt);
    nmiss  = malloc((size_t)NS * sizeof *nmiss);
    sedges = malloc((size_t)NS * sizeof *sedges);
    vlist  = malloc((size_t)NS * sizeof *vlist);
    vpos   = malloc((size_t)NS * sizeof *vpos);
    if (!cnt || !nmiss || !sedges || !vlist || !vpos){ fprintf(stderr, "alloc failed (NS=%ld)\n", NS); return 2; }

    /* enumerate (R+1)-subsets = 7 nested loops */
    long ns = 0;
    int v[R+1];
    for (v[0]=0; v[0]<N; v[0]++) for (v[1]=v[0]+1; v[1]<N; v[1]++) for (v[2]=v[1]+1; v[2]<N; v[2]++)
    for (v[3]=v[2]+1; v[3]<N; v[3]++) for (v[4]=v[3]+1; v[4]<N; v[4]++) for (v[5]=v[4]+1; v[5]<N; v[5]++)
    for (v[6]=v[5]+1; v[6]<N; v[6]++){
        int t = 0;
        for (int a = 0; a <= R; a++) for (int b = a+1; b <= R; b++) sedges[ns][t++] = eid[v[a]][v[b]];
        ns++;
    }
    if (ns != NS){ fprintf(stderr, "enum bug: ns=%ld NS=%ld\n", ns, NS); return 2; }

    /* per-edge subset lists */
    long *fill = calloc(E, sizeof(long));
    for (int e = 0; e < E; e++) esets[e] = malloc((size_t)edeg * sizeof(int32_t));
    for (long s = 0; s < NS; s++) for (int t = 0; t < EPS; t++){ int e = sedges[s][t]; esets[e][fill[e]++] = (int32_t)s; }
    for (int e = 0; e < E; e++) if (fill[e] != edeg){ fprintf(stderr, "edeg bug: edge %d has %ld want %ld\n", e, fill[e], edeg); return 2; }
    memset(vpos, -1, (size_t)NS * sizeof *vpos);

    /* init colouring: random, or from INIT.json (crude parser: reads ints after "colours") */
    if (argc >= 5 && strcmp(argv[4], "-") != 0){
        FILE *f = fopen(argv[4], "r"); if (!f){ perror("init"); return 2; }
        char *buf = malloc(1<<22); size_t L = fread(buf, 1, (1<<22)-1, f); buf[L] = 0; fclose(f);
        char *p = strstr(buf, "colours"); if (!p){ fprintf(stderr, "no colours key\n"); return 2; }
        int vals[NMAX*NMAX], nv2 = 0;
        for (; *p && nv2 < N*N; p++){
            if (*p == '-' || (*p >= '0' && *p <= '9')){
                vals[nv2++] = (int)strtol(p, &p, 10); p--;
            }
        }
        if (nv2 != N*N){ fprintf(stderr, "parsed %d ints, want %d\n", nv2, N*N); return 2; }
        for (int i = 0; i < N; i++) for (int j = i+1; j < N; j++){
            int c = vals[i*N+j];
            if (c < 0 || c >= R){ fprintf(stderr, "init colour %d out of range at (%d,%d)\n", c, i, j); return 2; }
            col[eid[i][j]] = c;
        }
        free(buf);
    } else {
        for (int e = 0; e < E; e++) col[e] = rnd() % R;
    }

    /* initial counts */
    nviol = 0;
    for (long s = 0; s < NS; s++){
        memset(cnt[s], 0, R);
        for (int t = 0; t < EPS; t++) cnt[s][col[sedges[s][t]]]++;
        nmiss[s] = 0;
        for (int c = 0; c < R; c++) if (!cnt[s][c]) nmiss[s]++;
        if (nmiss[s]) viol_add(s);
    }
    fprintf(stderr, "n=%d: %ld subsets, initial violations %d\n", N, NS, nviol);

    int best = nviol;
    int bestcol[EMAX]; memcpy(bestcol, col, sizeof col);
    long long step, last_improve = 0, last_dump = -1000000;
    time_t t_start = time(NULL), last_hb = 0;
    for (step = 0; step < maxsteps && nviol > 0; step++){
        int s = vlist[rnd() % nviol];
        /* random missing colour of s */
        int mc[R], nm = 0;
        for (int c = 0; c < R; c++) if (!cnt[s][c]) mc[nm++] = c;
        int c = mc[rnd() % nm];
        int e;
        /* Adaptive: bulk descent uses cheap sampled greedy (greedyk of 21 edges) + base noise;
         * the endgame (few violations) uses full greedy + low noise so it actually reaches 0 --
         * sampling too few edges cannot reliably find the moves that clear the last violations. */
        int endgame = (nviol < ENDGAME);
        int nz = endgame ? (noise < 5 ? noise : 5) : noise;
        if ((int)(rnd() % 100) < nz){                /* noise: random edge of s */
            e = sedges[s][rnd() % EPS];
        } else {                                     /* greedy: best delta among sampled edges of s */
            int gk = endgame ? EPS : greedyk;
            int bd = 1<<30; int cand[EPS], ncand = 0;
            int t0 = rnd() % EPS;
            for (int i = 0; i < gk; i++){
                int ee = sedges[s][(t0 + i) % EPS];
                int d = delta(ee, c);
                if (d < bd){ bd = d; ncand = 0; }
                if (d == bd) cand[ncand++] = ee;
            }
            e = cand[rnd() % ncand];
        }
        set_colour(e, c);
        if (nviol < best){
            best = nviol; last_improve = step;
            memcpy(bestcol, col, sizeof col);
            if (best < 500)
                fprintf(stderr, "step %lld: violations %d\n", step, best);
            if (bestout && step - last_dump > 200000){
                last_dump = step;
                int cur[EMAX]; memcpy(cur, col, sizeof col);
                for (int e2 = 0; e2 < E; e2++) col[e2] = bestcol[e2];
                FILE *f = fopen(bestout, "w");
                if (f){ write_json(f); fclose(f); }
                memcpy(col, cur, sizeof col);
            }
        }
        if (step - last_improve > 400000){           /* stagnation: restore best */
            for (int e2 = 0; e2 < E; e2++) if (col[e2] != bestcol[e2]) set_colour(e2, bestcol[e2]);
            last_improve = step;
        }
        if ((step & 0x3ff) == 0){                    /* time-based heartbeat (~every 30s) */
            time_t now = time(NULL);
            if (now - last_hb >= 30){
                last_hb = now;
                fprintf(stderr, "  ..t=%lds step %lld: cur %d best %d\n", (long)(now - t_start), step, nviol, best);
            }
        }
    }
    fprintf(stderr, "done at step %lld: violations %d (best seen %d)\n", step, nviol, best);
    if (bestout){
        int curcol[EMAX]; memcpy(curcol, col, sizeof col);
        for (int e2 = 0; e2 < E; e2++) col[e2] = bestcol[e2];
        FILE *f = fopen(bestout, "w");
        if (f){ write_json(f); fclose(f); }
        for (int e2 = 0; e2 < E; e2++) col[e2] = curcol[e2];
    }
    if (nviol == 0){ write_json(stdout); return 0; }
    return 1;
}
