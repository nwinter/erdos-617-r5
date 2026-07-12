/* locsearch_h4: balanced 5-colouring of K_n PLUS the h4 condition:
 * with T = {0,1,2,3} fixed, every 5-subset of V\T spans >= 1 colour-0 edge
 * (i.e. alpha(G_0 - T) <= 4). A zero-violation state at n=25 REFUTES chain
 * lemma MH'' and is a prime extension candidate. Derived from locsearch.c.
 *
 * Build:  cc -O2 -o tools/locsearch_h4 tools/locsearch_h4.c
 * Usage:  ./tools/locsearch_h4 N SEED MAXSTEPS [INIT [NOISE [BESTOUT]]]
 *
 * Original notes:
 * Minimizes the number of (r+1)-subsets missing at least one colour, by
 * focused random walk: pick a random violated subset, pick a random missing
 * colour c, recolour a random edge inside the subset to c (greedy tie-broken
 * by delta, with noise). Incremental scoring via per-subset colour counts.
 *
 * verify.py remains the referee: on reaching 0 violations this program prints
 * the colouring as JSON to stdout and exits 0; caller must run verify.py.
 *
 * Build:  cc -O2 -o tools/locsearch tools/locsearch.c
 * Usage:  ./tools/locsearch N SEED MAXSTEPS [INIT.json [NOISE_PCT [BESTOUT]]]
 *         INIT.json optional warm start (verify.py format, n=N); "-" = random.
 *         NOISE_PCT: random-edge probability in percent (default 25).
 *         BESTOUT: file to write best-seen colouring as JSON on exit.
 *         Progress to stderr; JSON to stdout only on success (0 violations).
 *         Stagnation policy: restore best state after 400k non-improving steps.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define R 5
#define NMAX 26
#define EMAX (NMAX*(NMAX-1)/2)

static int N, E, NS;                 /* vertices, edges, subsets */
static int eid[NMAX][NMAX];          /* edge id */
static int col[EMAX];                /* current colouring */
static uint8_t cnt[/*NS*/ 230230][R];/* per-subset colour counts */
static uint8_t nmiss[230230];        /* # colours with count 0 */
static int16_t sedges[230230][15];   /* edge ids of each subset */
static int32_t *esets[EMAX];         /* subsets containing edge e */
static int edeg;                     /* = C(N-2, R-1) subsets per edge */
static int *vlist, nviol;            /* violated subset ids, swap-remove */
static int *vpos;                    /* position of subset in vlist, -1 if absent */

/* h4 family: 5-subsets of {4..N-1}, each needs >= 1 colour-0 edge */
#define NS5MAX 20349                 /* C(21,5) at N=25 */
static int NS5;
static int16_t s5edges[NS5MAX][10];
static int32_t *e5sets[EMAX];
static int e5deg[EMAX];
static uint8_t cnt0[NS5MAX];
static int *v5list, nviol5, *v5pos;

static void v5_add(int s){ if (v5pos[s] < 0){ v5pos[s] = nviol5; v5list[nviol5++] = s; } }
static void v5_del(int s){ int p = v5pos[s]; if (p >= 0){ int t = v5list[--nviol5]; v5list[p] = t; v5pos[t] = p; v5pos[s] = -1; } }

static uint64_t rng;
static inline uint64_t rnd(void){ rng ^= rng<<13; rng ^= rng>>7; rng ^= rng<<17; return rng; }

static void viol_add(int s){ if (vpos[s] < 0){ vpos[s] = nviol; vlist[nviol++] = s; } }
static void viol_del(int s){ int p = vpos[s]; if (p >= 0){ int t = vlist[--nviol]; vlist[p] = t; vpos[t] = p; vpos[s] = -1; } }

/* recolour edge e to c, updating all structures; returns nothing */
static void set_colour(int e, int c){
    int old = col[e];
    if (old == c) return;
    col[e] = c;
    int32_t *ss = esets[e];
    for (int k = 0; k < edeg; k++){
        int s = ss[k];
        uint8_t *q = cnt[s];
        if (--q[old] == 0) if (++nmiss[s] == 1) viol_add(s);
        if (q[c]++ == 0) if (--nmiss[s] == 0) viol_del(s);
    }
    if ((old == 0 || c == 0) && e5deg[e]){
        int32_t *tt = e5sets[e];
        for (int k = 0; k < e5deg[e]; k++){
            int s = tt[k];
            if (old == 0){ if (--cnt0[s] == 0) v5_add(s); }
            if (c == 0){ if (cnt0[s]++ == 0) v5_del(s); }
        }
    }
}

/* delta in #violations if edge e -> colour c (no state change) */
static int delta(int e, int c){
    int old = col[e], d = 0;
    if (old == c) return 0;
    int32_t *ss = esets[e];
    for (int k = 0; k < edeg; k++){
        int s = ss[k];
        uint8_t *q = cnt[s];
        int m = nmiss[s];
        int m2 = m + (q[old] == 1) - (q[c] == 0);
        d += (m2 > 0) - (m > 0);
    }
    if ((old == 0 || c == 0) && e5deg[e]){
        int32_t *tt = e5sets[e];
        for (int k = 0; k < e5deg[e]; k++){
            int s = tt[k];
            int m = cnt0[s];
            int m2 = m - (old == 0) + (c == 0);
            d += (m2 == 0) - (m == 0);
        }
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
    rng = strtoull(argv[2], 0, 10) * 2654435761u + 1; for (int i = 0; i < 10; i++) rnd();
    long long maxsteps = atoll(argv[3]);
    int noise = (argc >= 6) ? atoi(argv[5]) : 25;
    const char *bestout = (argc >= 7) ? argv[6] : 0;

    E = 0;
    for (int i = 0; i < N; i++) for (int j = i+1; j < N; j++){ eid[i][j] = eid[j][i] = E++; }

    /* enumerate (R+1)-subsets */
    NS = 0;
    int v[R+1];
    for (v[0]=0; v[0]<N; v[0]++) for (v[1]=v[0]+1; v[1]<N; v[1]++) for (v[2]=v[1]+1; v[2]<N; v[2]++)
    for (v[3]=v[2]+1; v[3]<N; v[3]++) for (v[4]=v[3]+1; v[4]<N; v[4]++) for (v[5]=v[4]+1; v[5]<N; v[5]++){
        int t = 0;
        for (int a = 0; a <= R; a++) for (int b = a+1; b <= R; b++) sedges[NS][t++] = eid[v[a]][v[b]];
        NS++;
    }
    /* per-edge subset lists */
    int *fill = calloc(E, sizeof(int));
    edeg = NS * 15 / E;
    for (int e = 0; e < E; e++) esets[e] = malloc(edeg * sizeof(int32_t));
    for (int s = 0; s < NS; s++) for (int t = 0; t < 15; t++){ int e = sedges[s][t]; esets[e][fill[e]++] = s; }
    for (int e = 0; e < E; e++) if (fill[e] != edeg){ fprintf(stderr, "edeg bug\n"); return 2; }
    vlist = malloc(NS * sizeof(int)); vpos = malloc(NS * sizeof(int));
    memset(vpos, -1, NS * sizeof(int));

    /* enumerate h4 5-subsets of {4..N-1} and per-edge lists */
    NS5 = 0;
    {
        int w[5];
        for (w[0]=4; w[0]<N; w[0]++) for (w[1]=w[0]+1; w[1]<N; w[1]++) for (w[2]=w[1]+1; w[2]<N; w[2]++)
        for (w[3]=w[2]+1; w[3]<N; w[3]++) for (w[4]=w[3]+1; w[4]<N; w[4]++){
            int t = 0;
            for (int a = 0; a < 5; a++) for (int b = a+1; b < 5; b++) s5edges[NS5][t++] = eid[w[a]][w[b]];
            NS5++;
        }
    }
    memset(e5deg, 0, sizeof e5deg);
    for (int s = 0; s < NS5; s++) for (int t = 0; t < 10; t++) e5deg[s5edges[s][t]]++;
    for (int e = 0; e < E; e++) if (e5deg[e]) e5sets[e] = malloc(e5deg[e] * sizeof(int32_t));
    {
        int *f5 = calloc(E, sizeof(int));
        for (int s = 0; s < NS5; s++) for (int t = 0; t < 10; t++){ int e = s5edges[s][t]; e5sets[e][f5[e]++] = s; }
        free(f5);
    }
    v5list = malloc(NS5 * sizeof(int)); v5pos = malloc(NS5 * sizeof(int));
    memset(v5pos, -1, NS5 * sizeof(int));

    /* init colouring: random, or from INIT.json (crude parser: reads ints) */
    if (argc >= 5 && strcmp(argv[4], "-") != 0){
        FILE *f = fopen(argv[4], "r"); if (!f){ perror("init"); return 2; }
        /* expects "colours": [[...]] with n rows of n ints; parse all ints after "colours" */
        char *buf = malloc(1<<22); size_t L = fread(buf, 1, (1<<22)-1, f); buf[L] = 0; fclose(f);
        char *p = strstr(buf, "colours"); if (!p){ fprintf(stderr, "no colours key\n"); return 2; }
        int vals[NMAX*NMAX], nv2 = 0;
        for (; *p && nv2 < N*N; p++){
            if (*p == '-' || (*p >= '0' && *p <= '9')){
                vals[nv2++] = (int)strtol(p, &p, 10); p--;
            }
        }
        if (nv2 != N*N){ fprintf(stderr, "parsed %d ints, want %d\n", nv2, N*N); return 2; }
        for (int i = 0; i < N; i++) for (int j = i+1; j < N; j++) col[eid[i][j]] = vals[i*N+j];
    } else {
        for (int e = 0; e < E; e++) col[e] = rnd() % R;
    }

    /* initial counts */
    nviol = 0;
    for (int s = 0; s < NS; s++){
        memset(cnt[s], 0, R);
        for (int t = 0; t < 15; t++) cnt[s][col[sedges[s][t]]]++;
        nmiss[s] = 0;
        for (int c = 0; c < R; c++) if (!cnt[s][c]) nmiss[s]++;
        if (nmiss[s]) viol_add(s);
    }
    nviol5 = 0;
    for (int s = 0; s < NS5; s++){
        cnt0[s] = 0;
        for (int t = 0; t < 10; t++) if (col[s5edges[s][t]] == 0) cnt0[s]++;
        if (cnt0[s] == 0) v5_add(s);
    }
    fprintf(stderr, "n=%d: %d six-subsets + %d h4 five-subsets; initial violations %d + %d\n",
            N, NS, NS5, nviol, nviol5);

    int best = nviol + nviol5;
    int bestcol[EMAX]; memcpy(bestcol, col, sizeof col);
    long long step, last_improve = 0, last_dump = -1000000;
    for (step = 0; step < maxsteps && nviol + nviol5 > 0; step++){
        int total = nviol + nviol5;
        int r6 = (int)(rnd() % total) < nviol;
        int e, c;
        if (r6 && nviol > 0){
            int s = vlist[rnd() % nviol];
            int mc[R], nm = 0;
            for (int cc = 0; cc < R; cc++) if (!cnt[s][cc]) mc[nm++] = cc;
            c = mc[rnd() % nm];
            if ((int)(rnd() % 100) < noise){
                e = sedges[s][rnd() % 15];
            } else {
                int bd = 1<<30; int cand[15], ncand = 0;
                for (int t = 0; t < 15; t++){
                    int d = delta(sedges[s][t], c);
                    if (d < bd){ bd = d; ncand = 0; }
                    if (d == bd) cand[ncand++] = sedges[s][t];
                }
                e = cand[rnd() % ncand];
            }
        } else {
            int s = v5list[rnd() % nviol5];
            c = 0;                                   /* the 5-set needs a 0-edge */
            if ((int)(rnd() % 100) < noise){
                e = s5edges[s][rnd() % 10];
            } else {
                int bd = 1<<30; int cand[10], ncand = 0;
                for (int t = 0; t < 10; t++){
                    int d = delta(s5edges[s][t], 0);
                    if (d < bd){ bd = d; ncand = 0; }
                    if (d == bd) cand[ncand++] = s5edges[s][t];
                }
                e = cand[rnd() % ncand];
            }
        }
        set_colour(e, c);
        if (nviol + nviol5 < best){
            best = nviol + nviol5; last_improve = step;
            memcpy(bestcol, col, sizeof col);
            if (best < 50) fprintf(stderr, "step %lld: violations %d (%d+%d)\n", step, best, nviol, nviol5);
            if (bestout && best < 900 && step - last_dump > 200000){
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
        if ((step & 0xfffff) == 0)
            fprintf(stderr, "  ..step %lld: cur %d+%d best %d\n", step, nviol, nviol5, best);
    }
    fprintf(stderr, "done at step %lld: violations %d+%d (best seen %d)\n", step, nviol, nviol5, best);
    if (bestout){
        int curcol[EMAX]; memcpy(curcol, col, sizeof col);
        for (int e2 = 0; e2 < E; e2++) col[e2] = bestcol[e2];
        FILE *f = fopen(bestout, "w");
        if (f){ write_json(f); fclose(f); }
        for (int e2 = 0; e2 < E; e2++) col[e2] = curcol[e2];
    }
    if (nviol + nviol5 == 0){ write_json(stdout); return 0; }
    return 1;
}
