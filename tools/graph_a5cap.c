/* Phase-1 of the two-phase object-A hunt (task #77): find a SINGLE graph on n vertices with
 *   alpha(G) <= 5  (no independent 6-set)  AND  cap-16 (every 7-set spans <= 16 edges of G).
 * This is the class-0 candidate for object A at n=31, where class 0 provably cannot be a union
 * of cliques (cap-16 forbids K_7, and 5 cliques <=6 only reach 30 vertices). r6/feasibility.md
 * says >=98 edges are needed. If NO such graph is findable, that is a MAJOR finding (the
 * lemma-analogue may hold for structural reasons the fill argument can't see) -> escalate.
 *
 * Binary edge local search (flip present/absent), incremental two-family scoring:
 *   6-sets: cnt = #present edges; violation iff cnt==0 (independent 6-set => alpha>=6).
 *   7-sets: cnt = #present edges; violation iff cnt>=17 (cap-16 breached).
 * Move: pick a violated subset; an independent 6-set -> ADD an absent edge inside it; an
 * over-cap 7-set -> REMOVE a present edge inside it (greedy by delta, with noise).
 *
 * Build: cc -O3 -o tools/graph_a5cap tools/graph_a5cap.c
 * Usage: ./tools/graph_a5cap N SEED MAXSTEPS [NOISE [BESTOUT [GREEDYK]]]
 *   init = 5 balanced cliques (alpha=5 clean; only cap breached by any K_7) then search.
 *   On success (0 violations) prints the graph JSON {"n":N,"m":M,"adj":[[..]]} to stdout.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define NMAX 34
#define EPS7 21
#define EPS6 15
#define EMAX (NMAX*(NMAX-1)/2)
#define CAP 16
#define ENDGAME 1500

static int N, E;
static int eid[NMAX][NMAX], ev[EMAX][2];
static uint8_t present[EMAX];
static long NS7, edeg7, NS6, edeg6;
static uint8_t *cnt7, *bad7; static int16_t (*sedges7)[EPS7]; static int32_t *esets7[EMAX];
static uint8_t *cnt6, *bad6; static int16_t (*sedges6)[EPS6]; static int32_t *esets6[EMAX];
static int *vlist, nvit, *vpos; static long total;
static uint8_t fixedmask[EMAX];         /* BASE5K6: edges locked (cliques + v attachments/non-edges) */

static uint64_t rng; static inline uint64_t rnd(void){ rng^=rng<<13; rng^=rng>>7; rng^=rng<<17; return rng; }
static long nCk(int n,int k){ if(k<0||k>n)return 0; long r=1; for(int i=0;i<k;i++) r=r*(n-i)/(i+1); return r; }
static void vadd(int id){ if(vpos[id]<0){ vpos[id]=nvit; vlist[nvit++]=id; } }
static void vdel(int id){ int p=vpos[id]; if(p>=0){ int t=vlist[--nvit]; vlist[p]=t; vpos[t]=p; vpos[id]=-1; } }

static void flip(int e){                       /* toggle edge e present/absent */
    int d = present[e] ? -1 : +1; present[e] ^= 1;
    int32_t *s7=esets7[e];
    for(long i=0;i<edeg7;i++){ int s=s7[i]; int k=cnt7[s]; cnt7[s]=k+d;
        int nb=((k+d)>=17)-(k>=17); if(nb){ int b=bad7[s], v=b+nb; bad7[s]=v; total+=nb; if(b==0&&v>0)vadd(s); else if(b>0&&v==0)vdel(s);} }
    int32_t *s6=esets6[e];
    for(long i=0;i<edeg6;i++){ int t=s6[i]; int k=cnt6[t]; cnt6[t]=k+d;
        /* 6-set bad if empty (independent => alpha) OR full (K_6 => omega>5) */
        int nb=(((k+d)==0)-(k==0)) + (((k+d)==15)-(k==15)); if(nb){ int b=bad6[t], v=b+nb; bad6[t]=v; total+=nb; if(b==0&&v>0)vadd((int)(NS7+t)); else if(b>0&&v==0)vdel((int)(NS7+t)); } }
}
static int delta(int e){
    int d = present[e] ? -1 : +1, dv=0;
    int32_t *s7=esets7[e]; for(long i=0;i<edeg7;i++){ int k=cnt7[s7[i]]; dv += ((k+d)>=17)-(k>=17); }
    int32_t *s6=esets6[e]; for(long i=0;i<edeg6;i++){ int k=cnt6[s6[i]]; dv += (((k+d)==0)-(k==0)) + (((k+d)==15)-(k==15)); }
    return dv;
}

static int gcount(void){ int m=0; for(int e=0;e<E;e++)m+=present[e]; return m; }
static void write_graph(FILE*f, uint8_t*g){
    int m=0; for(int e=0;e<E;e++)m+=g[e];
    fprintf(f,"{\"n\":%d,\"m\":%d,\"adj\":[",N,m);
    for(int i=0;i<N;i++){ fprintf(f,"["); for(int j=0;j<N;j++) fprintf(f,"%d%s",(i!=j&&g[eid[i][j]])?1:0,j<N-1?",":""); fprintf(f,"]%s",i<N-1?",":""); }
    fprintf(f,"]}\n");
}

/* one focused-walk move: fix a random violated subset (remove from over-cap 7-set / add to
 * independent 6-set), greedy over greedyk sampled candidate edges with noise. */
static void do_move(int gk, int nz){
    int id=vlist[rnd()%nvit], cand[EPS7], nc=0;
    if(id<NS7){ int s=id;                          /* over-cap 7-set: remove a present edge */
        for(int t=0;t<EPS7;t++){ int e=sedges7[s][t]; if(present[e]&&!fixedmask[e]) cand[nc++]=e; } }
    else { int t=id-(int)NS7;
        if(cnt6[t]==0)                             /* independent 6-set (alpha): add an absent edge */
            for(int k=0;k<EPS6;k++){ int e=sedges6[t][k]; if(!present[e]&&!fixedmask[e]) cand[nc++]=e; }
        else                                       /* K_6 (omega>5): remove a present edge */
            for(int k=0;k<EPS6;k++){ int e=sedges6[t][k]; if(present[e]&&!fixedmask[e]) cand[nc++]=e; } }
    if(!nc) return;
    int e;
    if((int)(rnd()%100)<nz) e=cand[rnd()%nc];
    else { int bd=1<<30, b5[EPS7], nb=0, st=rnd()%nc, kk=gk<nc?gk:nc;
        for(int i=0;i<kk;i++){ int ee=cand[(st+i)%nc]; int d=delta(ee); if(d<bd){bd=d;nb=0;} if(d==bd)b5[nb++]=ee; }
        e=b5[rnd()%nb]; }
    flip(e);
}
/* greedily remove every edge whose removal keeps validity (delta==0) */
static void sparsify(void){
    int improved=1, order[EMAX];
    while(improved){ improved=0;
        for(int e=0;e<E;e++) order[e]=e;
        for(int e=E-1;e>0;e--){ int k=rnd()%(e+1); int t=order[e];order[e]=order[k];order[k]=t; }
        for(int i=0;i<E;i++){ int e=order[i]; if(present[e] && !fixedmask[e] && delta(e)==0){ flip(e); improved=1; } }
    }
}

int main(int argc,char**argv){
    if(argc<4){ fprintf(stderr,"usage: %s N SEED MAXSTEPS [NOISE [BESTOUT [GREEDYK]]]\n",argv[0]); return 2; }
    N=atoi(argv[1]); if(N<7||N>NMAX){fprintf(stderr,"N 7..%d\n",NMAX);return 2;}
    rng=strtoull(argv[2],0,10)*2654435761u+1; for(int i=0;i<10;i++)rnd();
    long long maxsteps=atoll(argv[3]);
    int noise=(argc>=5)?atoi(argv[4]):10; const char*bestout=(argc>=6)?argv[5]:0;
    int greedyk=(argc>=7)?atoi(argv[6]):6; if(greedyk<=0)greedyk=EPS7;

    E=0; for(int i=0;i<N;i++)for(int j=i+1;j<N;j++){ eid[i][j]=eid[j][i]=E; ev[E][0]=i; ev[E][1]=j; E++; }
    NS7=nCk(N,7); edeg7=nCk(N-2,5); NS6=nCk(N,6); edeg6=nCk(N-2,4);
    cnt7=calloc(NS7,1); bad7=calloc(NS7,1); sedges7=malloc((size_t)NS7*sizeof*sedges7);
    cnt6=calloc(NS6,1); bad6=calloc(NS6,1); sedges6=malloc((size_t)NS6*sizeof*sedges6);
    vlist=malloc((size_t)(NS7+NS6)*4); vpos=malloc((size_t)(NS7+NS6)*4);
    if(!cnt7||!sedges7||!cnt6||!sedges6||!vlist||!vpos){fprintf(stderr,"alloc\n");return 2;}
    { long ns=0; int v[7]; for(v[0]=0;v[0]<N;v[0]++)for(v[1]=v[0]+1;v[1]<N;v[1]++)for(v[2]=v[1]+1;v[2]<N;v[2]++)for(v[3]=v[2]+1;v[3]<N;v[3]++)
      for(v[4]=v[3]+1;v[4]<N;v[4]++)for(v[5]=v[4]+1;v[5]<N;v[5]++)for(v[6]=v[5]+1;v[6]<N;v[6]++){ int t=0; for(int a=0;a<7;a++)for(int b=a+1;b<7;b++) sedges7[ns][t++]=eid[v[a]][v[b]]; ns++; } if(ns!=NS7){fprintf(stderr,"e7\n");return 2;} }
    { long ns=0; int v[6]; for(v[0]=0;v[0]<N;v[0]++)for(v[1]=v[0]+1;v[1]<N;v[1]++)for(v[2]=v[1]+1;v[2]<N;v[2]++)for(v[3]=v[2]+1;v[3]<N;v[3]++)
      for(v[4]=v[3]+1;v[4]<N;v[4]++)for(v[5]=v[4]+1;v[5]<N;v[5]++){ int t=0; for(int a=0;a<6;a++)for(int b=a+1;b<6;b++) sedges6[ns][t++]=eid[v[a]][v[b]]; ns++; } if(ns!=NS6){fprintf(stderr,"e6\n");return 2;} }
    { long*f=calloc(E,sizeof(long)); for(int e=0;e<E;e++)esets7[e]=malloc((size_t)edeg7*4);
      for(long s=0;s<NS7;s++)for(int t=0;t<EPS7;t++){int e=sedges7[s][t]; esets7[e][f[e]++]=(int32_t)s;} free(f); }
    { long*f=calloc(E,sizeof(long)); for(int e=0;e<E;e++)esets6[e]=malloc((size_t)edeg6*4);
      for(long s=0;s<NS6;s++)for(int t=0;t<EPS6;t++){int e=sedges6[s][t]; esets6[e][f[e]++]=(int32_t)s;} free(f); }
    for(long i=0;i<NS7+NS6;i++) vpos[i]=-1;

    /* init: RANDP env => each edge present with prob RANDP% (explore non-clique basins);
     * else 5 balanced cliques (alpha=5 clean; a >=7-clique breaches cap, which the search fixes) */
    int part[NMAX], sz[5], base=N/5, ext=N%5, v=0;
    for(int p=0;p<5;p++){ sz[p]=base+(p<ext?1:0); for(int q=0;q<sz[p];q++) part[v++]=p; }
    const char *rp = getenv("RANDP");
    if(getenv("BASE5K6")){          /* team-lead family: 5 K6 (v 0..29) + v=30 (1 edge/clique); search only between-clique */
        if(N!=31){ fprintf(stderr,"BASE5K6 expects N=31\n"); return 2; }
        for(int e=0;e<E;e++){
            int a=ev[e][0], b=ev[e][1];
            if(a<30 && b<30){
                if(a/6==b/6){ present[e]=1; fixedmask[e]=1; }   /* clique edge: fixed present */
                else        { present[e]=0; fixedmask[e]=0; }   /* between-clique: SEARCHABLE */
            } else {                                            /* edge to v=30 */
                int u=(a==30)?b:a;
                if(u%6==0){ present[e]=1; fixedmask[e]=1; }      /* v attaches to first of each clique */
                else      { present[e]=0; fixedmask[e]=1; }      /* v non-attachment: fixed absent */
            }
        }
    }
    else if(rp){ int pp=atoi(rp); for(int e=0;e<E;e++) present[e] = ((int)(rnd()%100) < pp); }
    else for(int e=0;e<E;e++) present[e] = (part[ev[e][0]]==part[ev[e][1]]);
    for(long s=0;s<NS7;s++){ int c=0; for(int t=0;t<EPS7;t++) c+=present[sedges7[s][t]]; cnt7[s]=c; bad7[s]=(c>=17); if(bad7[s])vadd((int)s); }
    for(long t=0;t<NS6;t++){ int c=0; for(int e=0;e<EPS6;e++) c+=present[sedges6[t][e]]; cnt6[t]=c; bad6[t]=(c==0)+(c==15); if(bad6[t])vadd((int)(NS7+t)); }
    total=0; for(long s=0;s<NS7;s++)total+=bad7[s]; for(long t=0;t<NS6;t++)total+=bad6[t];
    int m=0; for(int e=0;e<E;e++)m+=present[e];
    fprintf(stderr,"n=%d init: m=%d edges, violations total=%ld (clique sizes",N,m,total);
    for(int p=0;p<5;p++)fprintf(stderr," %d",sz[p]); fprintf(stderr,")\n");

    long best=total; uint8_t bestp[EMAX]; memcpy(bestp,present,E);
    long long step,last_imp=0,last_dump=-1000000; time_t t0=time(NULL),lhb=0;
    for(step=0; step<maxsteps && total>0; step++){
        int endgame=(total<ENDGAME), gk=endgame?EPS7:greedyk, nz=endgame?(noise<4?noise:4):noise;
        do_move(gk, nz);
        if(total<best){ best=total; last_imp=step; memcpy(bestp,present,E);
            if(best<300) fprintf(stderr,"step %lld: violations %ld\n",step,best);
            if(bestout && step-last_dump>200000){ last_dump=step; FILE*f=fopen(bestout,"w");
                if(f){ int mm=0;for(int x=0;x<E;x++)mm+=bestp[x]; fprintf(f,"{\"n\":%d,\"m\":%d,\"adj\":[",N,mm);
                    for(int i=0;i<N;i++){fprintf(f,"[");for(int j=0;j<N;j++)fprintf(f,"%d%s",(i!=j&&bestp[eid[i][j]])?1:0,j<N-1?",":"");fprintf(f,"]%s",i<N-1?",":"");}
                    fprintf(f,"]}\n"); fclose(f);} } }
        if(step-last_imp>400000){ for(int x=0;x<E;x++) if(present[x]!=bestp[x]) flip(x); last_imp=step; }
        if((step&0x3ff)==0){ time_t now=time(NULL); if(now-lhb>=30){ lhb=now; int mm=0;for(int x=0;x<E;x++)mm+=present[x];
            fprintf(stderr,"  ..t=%lds step %lld: cur %ld best %ld (m=%d)\n",(long)(now-t0),step,total,best,mm); } }
    }
    /* if valid: sparsify, then LNS minimisation (MINROUNDS rounds) to push edges toward the
     * ~98-115 range object A needs (so classes 1..5 can each reach alpha<=6). */
    if(total==0){
        sparsify();
        uint8_t bv[EMAX]; memcpy(bv,present,E); int bm=gcount();
        int rounds = getenv("MINROUNDS") ? atoi(getenv("MINROUNDS")) : 0;
        int kick = getenv("KICK") ? atoi(getenv("KICK")) : 10;
        for(int r=0; r<rounds; r++){
            memcpy(present,bv,E);                                   /* start from current best-valid */
            nvit=0; for(long i=0;i<NS7+NS6;i++) vpos[i]=-1;         /* rebuild cnt/bad/viol from present */
            for(long s=0;s<NS7;s++){ int c=0; for(int t=0;t<EPS7;t++) c+=present[sedges7[s][t]]; cnt7[s]=c; bad7[s]=(c>=17); if(bad7[s])vadd((int)s); }
            for(long t=0;t<NS6;t++){ int c=0; for(int e=0;e<EPS6;e++) c+=present[sedges6[t][e]]; cnt6[t]=c; bad6[t]=(c==0)+(c==15); if(bad6[t])vadd((int)(NS7+t)); }
            total=0; for(long s=0;s<NS7;s++)total+=bad7[s]; for(long t=0;t<NS6;t++)total+=bad6[t];
            int avail=0; for(int e=0;e<E;e++) if(present[e]&&!fixedmask[e]) avail++;
            int kk=kick<avail?kick:avail;
            for(int k=0;k<kk;k++){ int e; do{ e=rnd()%E; }while(!present[e]||fixedmask[e]); flip(e); }  /* remove searchable edges */
            long st; for(st=0; st<3000000 && total>0; st++){ int eg=(total<ENDGAME); do_move(eg?EPS7:greedyk, eg?3:noise); }
            if(total==0){ sparsify(); int m=gcount(); if(m<bm){ bm=m; memcpy(bv,present,E);
                fprintf(stderr,"  LNS round %d: new best m=%d\n", r, bm);
                if(bestout){ FILE*f=fopen(bestout,"w"); if(f){ write_graph(f,bv); fclose(f); } } } }
        }
        memcpy(present,bv,E);
        nvit=0; for(long i=0;i<NS7+NS6;i++) vpos[i]=-1;
        for(long s=0;s<NS7;s++){ int c=0; for(int t=0;t<EPS7;t++) c+=present[sedges7[s][t]]; cnt7[s]=c; bad7[s]=(c>=17); }
        for(long t=0;t<NS6;t++){ int c=0; for(int e=0;e<EPS6;e++) c+=present[sedges6[t][e]]; cnt6[t]=c; bad6[t]=(c==0)+(c==15); }
        total=0; for(long s=0;s<NS7;s++)total+=bad7[s]; for(long t=0;t<NS6;t++)total+=bad6[t];
    }
    int mm=gcount();
    fprintf(stderr,"done step %lld: violations %ld (best %ld, m=%d after sparsify+LNS)\n",step,total,best,mm);
    if(total==0){ printf("{\"n\":%d,\"m\":%d,\"adj\":[",N,mm);
        for(int i=0;i<N;i++){printf("[");for(int j=0;j<N;j++)printf("%d%s",(i!=j&&present[eid[i][j]])?1:0,j<N-1?",":"");printf("]%s",i<N-1?",":"");}
        printf("]}\n"); return 0; }
    return 1;
}
