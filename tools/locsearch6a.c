/* Local search for the r=6 "object A" — the 5-blocker that would refute the [MH2]-analogue.
 *
 * Target (task #77, team-lead spec; r6/feasibility.md): a 6-colouring of K_n (primary n=31) with
 *   (1) cap-16 : every 7-set spans <=16 edges of any single colour class;
 *   (2) alpha(G_0) <= 5 : colour class 0 has NO independent 6-set (every 6-set has a colour-0 edge);
 *   (3) alpha(G_c) <= 6 for c=1..5 : no independent 7-set (every 7-set has a colour-c edge).
 * NO balance requirement is imposed. If such an object exists at n=31 the fill argument is chasing
 * a false statement. (An independent brute checker, tools/checkA.py, re-verifies any hit and also
 * reports omega and balance, so we document exactly which statement each hit refutes.)
 *
 * Unlike the balance search this needs TWO subset families:
 *   - 7-subsets: colour counts drive (3) [missing colour c in 1..5] and (1) [count >= 17 = cap].
 *   - 6-subsets: colour-0 count drives (2) [count == 0 = independent 6-set in class 0].
 * Incremental scoring mirrors locsearch6's per-edge subset lists; the per-subset "badness" logic is
 * richer (missing-colour + cap on 7-sets, colour-0-absent on 6-sets) but each recolour is still
 * O(edeg7 + edeg6). The 6-family is only touched when the recolour involves colour 0.
 *
 * Build:  cc -O3 -o tools/locsearch6a tools/locsearch6a.c
 * Usage:  ./tools/locsearch6a N SEED MAXSTEPS [INIT.json|- [NOISE_PCT [BESTOUT [GREEDYK]]]]
 *         JSON of a 0-violation object -> stdout on success; best-seen -> BESTOUT; progress -> stderr.
 *         MAXSTEPS=0 => score the init and print the component breakdown (V_cap/V_missed/V_alpha0).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define R 6
#define NMAX 34
#define EPS7 21                        /* C(7,2) */
#define EPS6 15                        /* C(6,2) */
#define EMAX (NMAX*(NMAX-1)/2)
#define CAP 16                         /* forbidden threshold is >=17 in a 7-set */
#define ENDGAME 2000

static int N, E;
static int eid[NMAX][NMAX];
static int col[EMAX];

static long NS7, edeg7;
static uint8_t (*cnt7)[R];             /* colour counts per 7-set */
static uint8_t *bad7;                  /* (#c in 1..5 with cnt==0) + (#c with cnt>=17) */
static int16_t (*sedges7)[EPS7];
static int32_t *esets7[EMAX];

static long NS6, edeg6;
static uint8_t *cnt6_0;                /* colour-0 count per 6-set */
static uint8_t *bad6;                  /* 1 iff cnt6_0==0 (independent 6-set in class 0) */
static int16_t (*sedges6)[EPS6];
static int32_t *esets6[EMAX];

static int *vlist, nvitems;            /* violated item ids: [0,NS7) = 7-sets, [NS7,NS7+NS6) = 6-sets */
static int *vpos;
static long total;                     /* objective = sum of bad7 + sum of bad6 */
static uint8_t frozen[EMAX];           /* FREEZE0 mode: class-0 (clique) edges, never recoloured */
static int freeze0 = 0;                /* Phase-2: class 0 fixed, only optimise between-edges 1..5 */

static uint64_t rng;
static inline uint64_t rnd(void){ rng ^= rng<<13; rng ^= rng>>7; rng ^= rng<<17; return rng; }

static long nCk(int n, int k){ if (k<0||k>n) return 0; long r=1; for (int i=0;i<k;i++) r=r*(n-i)/(i+1); return r; }

static void viol_add(int id){ if (vpos[id] < 0){ vpos[id] = nvitems; vlist[nvitems++] = id; } }
static void viol_del(int id){ int p = vpos[id]; if (p >= 0){ int t = vlist[--nvitems]; vlist[p] = t; vpos[t] = p; vpos[id] = -1; } }

/* recolour edge e to c, updating all structures and `total` */
static void set_colour(int e, int c){
    int old = col[e];
    if (old == c) return;
    col[e] = c;
    /* 7-family */
    int32_t *ss = esets7[e];
    for (long i = 0; i < edeg7; i++){
        int s = ss[i];
        uint8_t *q = cnt7[s];
        int k = q[old], m = q[c];
        q[old] = k - 1; q[c] = m + 1;
        int db = 0;
        if (old >= 1 && k == 1) db += 1;          /* old (in 1..5) becomes missing */
        if (k == 17) db -= 1;                      /* old drops below cap threshold */
        if (c >= 1 && m == 0) db -= 1;             /* c (in 1..5) becomes present */
        if (m == 16) db += 1;                      /* c crosses cap threshold */
        if (db){
            int b = bad7[s], nb = b + db;
            bad7[s] = nb; total += db;
            if (b == 0 && nb > 0) viol_add(s);
            else if (b > 0 && nb == 0) viol_del(s);
        }
    }
    /* 6-family: only colour-0 accounting changes */
    if (old == 0 || c == 0){
        int32_t *tt = esets6[e];
        for (long i = 0; i < edeg6; i++){
            int t = tt[i];
            int k0 = cnt6_0[t];
            if (old == 0) k0--; if (c == 0) k0++;
            cnt6_0[t] = k0;
            int after = (k0 == 0);
            if (after != bad6[t]){
                int db = after - bad6[t];
                bad6[t] = after; total += db;
                if (db > 0) viol_add((int)(NS7 + t)); else viol_del((int)(NS7 + t));
            }
        }
    }
}

/* change in `total` if edge e -> colour c (no state change) */
static int delta(int e, int c){
    int old = col[e], d = 0;
    if (old == c) return 0;
    int32_t *ss = esets7[e];
    for (long i = 0; i < edeg7; i++){
        int s = ss[i];
        uint8_t *q = cnt7[s];
        int k = q[old], m = q[c];
        if (old >= 1 && k == 1) d += 1;
        if (k == 17) d -= 1;
        if (c >= 1 && m == 0) d -= 1;
        if (m == 16) d += 1;
    }
    if (old == 0 || c == 0){
        int32_t *tt = esets6[e];
        for (long i = 0; i < edeg6; i++){
            int t = tt[i];
            int k0 = cnt6_0[t], k1 = k0 + (c==0) - (old==0);
            d += (k1 == 0) - (k0 == 0);
        }
    }
    return d;
}

/* pick an edge from cand[0..nc-1] to recolour to c: sampled-greedy (best delta of gk) or noise-random */
static int pick_edge(int *cand, int nc, int c, int gk, int nz){
    if (nc == 1) return cand[0];
    if ((int)(rnd()%100) < nz) return cand[rnd()%nc];
    int bd = 1<<30, best[EPS7], nb = 0;
    int start = rnd()%nc, kk = gk < nc ? gk : nc;
    for (int i = 0; i < kk; i++){
        int e = cand[(start+i)%nc];
        int d = delta(e, c);
        if (d < bd){ bd = d; nb = 0; }
        if (d == bd) best[nb++] = e;
    }
    return best[rnd()%nb];
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
    if (argc < 4){ fprintf(stderr, "usage: %s N SEED MAXSTEPS [INIT.json|- [NOISE [BESTOUT [GREEDYK]]]]\n", argv[0]); return 2; }
    N = atoi(argv[1]);
    if (N < 7 || N > NMAX){ fprintf(stderr, "N in 7..%d\n", NMAX); return 2; }
    rng = strtoull(argv[2],0,10) * 2654435761u + 1; for (int i=0;i<10;i++) rnd();
    long long maxsteps = atoll(argv[3]);
    int noise = (argc >= 6) ? atoi(argv[5]) : 15;
    const char *bestout = (argc >= 7) ? argv[6] : 0;
    int greedyk = (argc >= 8) ? atoi(argv[7]) : 4;
    if (greedyk <= 0) greedyk = EPS7;

    E = 0;
    for (int i=0;i<N;i++) for (int j=i+1;j<N;j++){ eid[i][j]=eid[j][i]=E++; }

    NS7 = nCk(N,7); edeg7 = nCk(N-2,5);
    NS6 = nCk(N,6); edeg6 = nCk(N-2,4);
    cnt7 = malloc((size_t)NS7*sizeof *cnt7);  bad7 = calloc(NS7,1);  sedges7 = malloc((size_t)NS7*sizeof *sedges7);
    cnt6_0 = malloc((size_t)NS6);             bad6 = calloc(NS6,1);  sedges6 = malloc((size_t)NS6*sizeof *sedges6);
    vlist = malloc((size_t)(NS7+NS6)*sizeof(int)); vpos = malloc((size_t)(NS7+NS6)*sizeof(int));
    if (!cnt7||!bad7||!sedges7||!cnt6_0||!bad6||!sedges6||!vlist||!vpos){ fprintf(stderr,"alloc fail\n"); return 2; }

    /* enumerate 7-subsets */
    { long ns=0; int v[7];
      for(v[0]=0;v[0]<N;v[0]++)for(v[1]=v[0]+1;v[1]<N;v[1]++)for(v[2]=v[1]+1;v[2]<N;v[2]++)for(v[3]=v[2]+1;v[3]<N;v[3]++)
      for(v[4]=v[3]+1;v[4]<N;v[4]++)for(v[5]=v[4]+1;v[5]<N;v[5]++)for(v[6]=v[5]+1;v[6]<N;v[6]++){
          int t=0; for(int a=0;a<7;a++)for(int b=a+1;b<7;b++) sedges7[ns][t++]=eid[v[a]][v[b]]; ns++;
      }
      if (ns!=NS7){ fprintf(stderr,"enum7 bug\n"); return 2; } }
    /* enumerate 6-subsets */
    { long ns=0; int v[6];
      for(v[0]=0;v[0]<N;v[0]++)for(v[1]=v[0]+1;v[1]<N;v[1]++)for(v[2]=v[1]+1;v[2]<N;v[2]++)for(v[3]=v[2]+1;v[3]<N;v[3]++)
      for(v[4]=v[3]+1;v[4]<N;v[4]++)for(v[5]=v[4]+1;v[5]<N;v[5]++){
          int t=0; for(int a=0;a<6;a++)for(int b=a+1;b<6;b++) sedges6[ns][t++]=eid[v[a]][v[b]]; ns++;
      }
      if (ns!=NS6){ fprintf(stderr,"enum6 bug\n"); return 2; } }
    /* per-edge subset lists */
    { long *f7=calloc(E,sizeof(long)); for(int e=0;e<E;e++) esets7[e]=malloc((size_t)edeg7*4);
      for(long s=0;s<NS7;s++)for(int t=0;t<EPS7;t++){int e=sedges7[s][t]; esets7[e][f7[e]++]=(int32_t)s;}
      for(int e=0;e<E;e++) if(f7[e]!=edeg7){fprintf(stderr,"edeg7 bug\n");return 2;} free(f7); }
    { long *f6=calloc(E,sizeof(long)); for(int e=0;e<E;e++) esets6[e]=malloc((size_t)edeg6*4);
      for(long s=0;s<NS6;s++)for(int t=0;t<EPS6;t++){int e=sedges6[s][t]; esets6[e][f6[e]++]=(int32_t)s;}
      for(int e=0;e<E;e++) if(f6[e]!=edeg6){fprintf(stderr,"edeg6 bug\n");return 2;} free(f6); }
    for(long i=0;i<NS7+NS6;i++) vpos[i]=-1;

    /* init colouring */
    if (argc>=5 && strcmp(argv[4],"-")!=0){
        FILE *f=fopen(argv[4],"r"); if(!f){perror("init");return 2;}
        char *buf=malloc(1<<22); size_t L=fread(buf,1,(1<<22)-1,f); buf[L]=0; fclose(f);
        char *p=strstr(buf,"colours"); if(!p){fprintf(stderr,"no colours\n");return 2;}
        int vals[NMAX*NMAX], nv=0;
        for(;*p&&nv<N*N;p++) if(*p=='-'||(*p>='0'&&*p<='9')){ vals[nv++]=(int)strtol(p,&p,10); p--; }
        if(nv!=N*N){fprintf(stderr,"parsed %d want %d\n",nv,N*N);return 2;}
        for(int i=0;i<N;i++)for(int j=i+1;j<N;j++){int c=vals[i*N+j]; if(c<0||c>=R){fprintf(stderr,"bad col\n");return 2;} col[eid[i][j]]=c;}
        free(buf);
    } else { for(int e=0;e<E;e++) col[e]=rnd()%R; }

    /* FREEZE0 (Phase-2): fix class 0 exactly as seeded (the clique edges), search only 1..5 */
    freeze0 = (getenv("FREEZE0") != NULL);
    if (freeze0){
        int nf = 0;
        for (int e = 0; e < E; e++){ frozen[e] = (col[e] == 0); nf += frozen[e]; }
        fprintf(stderr, "FREEZE0: class 0 fixed (%d frozen edges); optimising only colours 1..5\n", nf);
    }

    /* initial counts + component breakdown */
    long Vcap=0, Vmiss=0, Valpha0=0;
    for(long s=0;s<NS7;s++){
        uint8_t *q=cnt7[s]; memset(q,0,R);
        for(int t=0;t<EPS7;t++) q[col[sedges7[s][t]]]++;
        int b=0;
        for(int c=0;c<R;c++){ if(c>=1&&q[c]==0){b++;Vmiss++;} if(q[c]>=17){b++;Vcap++;} }
        bad7[s]=b; if(b) viol_add((int)s);
    }
    for(long t=0;t<NS6;t++){
        int k0=0; for(int e=0;e<EPS6;e++) if(col[sedges6[t][e]]==0) k0++;
        cnt6_0[t]=k0; bad6[t]=(k0==0); if(bad6[t]){Valpha0++; viol_add((int)(NS7+t));}
    }
    total = Vcap + Vmiss + Valpha0;
    fprintf(stderr,"n=%d: 7-sets %ld, 6-sets %ld; init violations total=%ld (cap=%ld missed=%ld alpha0=%ld)\n",
            N, NS7, NS6, total, Vcap, Vmiss, Valpha0);

    long best=total; int bestcol[EMAX]; memcpy(bestcol,col,sizeof col);
    long long step, last_improve=0, last_dump=-1000000; time_t t0=time(NULL), last_hb=0;
    for(step=0; step<maxsteps && total>0; step++){
        int id = vlist[rnd()%nvitems];
        int endgame = (total < ENDGAME);
        int gk = endgame ? EPS7 : greedyk;
        int nz = endgame ? (noise<5?noise:5) : noise;
        if (id < NS7){                                   /* 7-set: missing colour (1..5) and/or cap-excess */
            int s = id;
            int missed[5], nm=0, exc[6], ne=0;
            for(int c=1;c<R;c++) if(cnt7[s][c]==0) missed[nm++]=c;
            for(int c=0;c<R;c++) if(cnt7[s][c]>=17) exc[ne++]=c;
            if (nm>0 && (ne==0 || (rnd()&1))){           /* add a missing colour (common case) */
                int c = missed[rnd()%nm];
                int cand[EPS7], nc=0;                     /* in FREEZE0 exclude the fixed class-0 edges */
                for(int t=0;t<EPS7;t++){ int e=sedges7[s][t]; if(!freeze0 || !frozen[e]) cand[nc++]=e; }
                if (nc) set_colour(pick_edge(cand,nc,c,gk,nz), c);
            } else if (ne>0){                            /* reduce an over-cap colour (rare) */
                int c = exc[rnd()%ne];
                int cand[EPS7], nc=0; for(int t=0;t<EPS7;t++){ int e=sedges7[s][t]; if(col[e]==c && (!freeze0||!frozen[e])) cand[nc++]=e; }
                if (nc){
                    int e = cand[rnd()%nc];
                    int bd=1<<30, bc=-1;                 /* greedy target colour != c (exclude 0 in FREEZE0) */
                    for(int cc=(freeze0?1:0);cc<R;cc++){ if(cc==c) continue; int d=delta(e,cc); if(d<bd){bd=d;bc=cc;} }
                    if (bc>=0) set_colour(e, bc);
                }
            }
        } else if (!freeze0){                            /* 6-set: colour 0 absent -> add colour 0 */
            int t = id - (int)NS7;
            int cand[EPS6]; for(int k=0;k<EPS6;k++) cand[k]=sedges6[t][k];
            set_colour(pick_edge(cand,EPS6,0,gk,nz), 0);
        }
        /* (in FREEZE0 a violated 6-set is unfixable — means the seeded class 0 has alpha>5; the
         *  init breakdown's alpha0>0 flags that. Such a subset is skipped, total won't reach 0.) */
        if (total < best){
            best=total; last_improve=step; memcpy(bestcol,col,sizeof col);
            if (best < 400) fprintf(stderr,"step %lld: violations %ld\n", step, best);
            if (bestout && step-last_dump > 200000){
                last_dump=step; int cur[EMAX]; memcpy(cur,col,sizeof col);
                for(int e=0;e<E;e++) col[e]=bestcol[e];
                FILE *f=fopen(bestout,"w"); if(f){write_json(f);fclose(f);} memcpy(col,cur,sizeof col);
            }
        }
        if (step-last_improve > 400000){                 /* stagnation restore */
            for(int e=0;e<E;e++) if(col[e]!=bestcol[e]) set_colour(e,bestcol[e]);
            last_improve=step;
        }
        if ((step & 0x3ff)==0){ time_t now=time(NULL); if(now-last_hb>=30){ last_hb=now;
            fprintf(stderr,"  ..t=%lds step %lld: cur %ld best %ld\n",(long)(now-t0),step,total,best); } }
    }
    fprintf(stderr,"done at step %lld: violations %ld (best %ld)\n", step, total, best);
    if (bestout){ int cur[EMAX]; memcpy(cur,col,sizeof col); for(int e=0;e<E;e++) col[e]=bestcol[e];
        FILE *f=fopen(bestout,"w"); if(f){write_json(f);fclose(f);} for(int e=0;e<E;e++) col[e]=cur[e]; }
    if (total==0){ write_json(stdout); return 0; }
    return 1;
}
