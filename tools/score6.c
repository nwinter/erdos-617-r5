/* Fast standalone violation scorer for r=6 balanced-colouring candidates.
 *
 * Reads a verify.py-format JSON colouring ({"r":6,"n":N,"colours":[[...]]}) and counts the
 * number of 7-subsets that MISS at least one colour -- exactly verify.py's definition, but in
 * C so it is fast enough to score n=36 (C(36,7)=8.35M subsets) in well under a second.
 *
 * Purpose: (a) score baseline constructions; (b) an INDEPENDENT cross-check of locsearch6's
 * incremental count and of the referee (verify.py) on small cases -- three-way agreement.
 * It is NOT the referee; verify.py is. Minimal memory (just the colour matrix).
 *
 * Build:  cc -O3 -o tools/score6 tools/score6.c
 * Usage:  ./tools/score6 CANDIDATE.json      # prints "score6: n=N V violations of TOTAL"
 * Exit:   0 if 0 violations, 1 if >0, 2 on malformed input.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define R 6
#define NMAX 40

static int M[NMAX][NMAX];

static long read_int_after(const char *buf, const char *key){
    const char *p = strstr(buf, key);
    if (!p) return -1;
    p += strlen(key);
    while (*p && *p != '-' && !(*p >= '0' && *p <= '9')) p++;
    return strtol(p, 0, 10);
}

int main(int argc, char **argv){
    if (argc != 2){ fprintf(stderr, "usage: %s CANDIDATE.json\n", argv[0]); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f){ perror("open"); return 2; }
    char *buf = malloc(1<<22); size_t L = fread(buf, 1, (1<<22)-1, f); buf[L] = 0; fclose(f);

    long r = read_int_after(buf, "\"r\"");
    long n = read_int_after(buf, "\"n\"");
    if (r != R){ fprintf(stderr, "score6 only handles r=%d (got r=%ld)\n", R, r); return 2; }
    if (n < R+1 || n > NMAX){ fprintf(stderr, "n=%ld out of range\n", n); return 2; }
    int N = (int)n;

    /* parse the n*n matrix (crude int scan after "colours") */
    char *p = strstr(buf, "colours"); if (!p){ fprintf(stderr, "no colours key\n"); return 2; }
    int nv = 0;
    for (; *p && nv < N*N; p++){
        if (*p == '-' || (*p >= '0' && *p <= '9')){
            int v = (int)strtol(p, &p, 10); p--;
            M[nv / N][nv % N] = v; nv++;
        }
    }
    if (nv != N*N){ fprintf(stderr, "parsed %d ints, want %d\n", nv, N*N); return 2; }
    free(buf);

    /* sanity: symmetric, diagonal -1, off-diagonal in 0..R-1 */
    for (int i = 0; i < N; i++){
        if (M[i][i] != -1){ fprintf(stderr, "diag (%d,%d)=%d not -1\n", i, i, M[i][i]); return 2; }
        for (int j = i+1; j < N; j++){
            if (M[i][j] != M[j][i]){ fprintf(stderr, "asymmetric at (%d,%d)\n", i, j); return 2; }
            if (M[i][j] < 0 || M[i][j] >= R){ fprintf(stderr, "colour %d out of range at (%d,%d)\n", M[i][j], i, j); return 2; }
        }
    }

    const int full = (1 << R) - 1;
    long total = 0, viol = 0;
    int a,b,c,d,e,g,h;
    for (a=0;   a<N; a++)
    for (b=a+1; b<N; b++)
    for (c=b+1; c<N; c++)
    for (d=c+1; d<N; d++)
    for (e=d+1; e<N; e++)
    for (g=e+1; g<N; g++)
    for (h=g+1; h<N; h++){
        total++;
        int seen = 0;
        seen |= 1<<M[a][b]; seen |= 1<<M[a][c]; seen |= 1<<M[a][d]; seen |= 1<<M[a][e]; seen |= 1<<M[a][g]; seen |= 1<<M[a][h];
        seen |= 1<<M[b][c]; seen |= 1<<M[b][d]; seen |= 1<<M[b][e]; seen |= 1<<M[b][g]; seen |= 1<<M[b][h];
        seen |= 1<<M[c][d]; seen |= 1<<M[c][e]; seen |= 1<<M[c][g]; seen |= 1<<M[c][h];
        seen |= 1<<M[d][e]; seen |= 1<<M[d][g]; seen |= 1<<M[d][h];
        seen |= 1<<M[e][g]; seen |= 1<<M[e][h];
        seen |= 1<<M[g][h];
        if (seen != full) viol++;
    }
    printf("score6: n=%d %ld violations of %ld\n", N, viol, total);
    return viol == 0 ? 0 : 1;
}
