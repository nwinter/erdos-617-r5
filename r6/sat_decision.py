#!/usr/bin/env python3
"""DECISIVE SAT: does an (alpha<=5, omega<=5) graph with e<=120 exist on 31 vtcs?
(no cap-16 -- cleaner; UNSAT here => object A impossible even before cap => [MH''] TRUE;
 SAT here => m*(no cap)<=120, strong evidence window survives.)
Lazy CEGAR on BOTH alpha and omega, atmost-120."""
import sys, time, json
from itertools import combinations
from pysat.solvers import Cadical195
from pysat.card import CardEnc, EncType
N=31; FULL=(1<<N)-1
pairs=list(combinations(range(N),2)); vid={p:i+1 for i,p in enumerate(pairs)}; TOP=len(pairs)
def lit(a,b): return vid[(min(a,b),max(a,b))]
def adjbm(model):
    ms=set(v for v in model if v>0); adj=[0]*N
    for p in pairs:
        if vid[p] in ms: a,b=p; adj[a]|=1<<b; adj[b]|=1<<a
    return adj
def fc(adj,k,cand=None,chosen=0):
    if cand is None: cand=FULL
    if bin(chosen).count("1")==k: return chosen
    c=cand
    while c:
        v=(c&-c).bit_length()-1; c&=c-1
        if chosen&~adj[v]: continue
        r=fc(adj,k,cand&adj[v]&~((1<<(v+1))-1),chosen|(1<<v))
        if r is not None: return r
    return None
def indep(adj,k):
    comp=[(~adj[v])&FULL&~(1<<v) for v in range(N)]; return fc(comp,k)

def run(E, tlim=2400):
    t0=time.time(); s=Cadical195()
    enc=CardEnc.atmost(lits=list(vid.values()),bound=E,top_id=TOP,encoding=EncType.seqcounter)
    for cl in enc.clauses: s.add_clause(cl)
    rnd=0
    while time.time()-t0<tlim:
        rnd+=1
        if not s.solve():
            print(f"UNSAT at E<={E} after {rnd} rounds ({time.time()-t0:.0f}s) => m*(no cap) > {E} => object A IMPOSSIBLE => [MH''] TRUE",flush=True)
            return "UNSAT"
        adj=adjbm(s.get_model())
        i6=indep(adj,6)
        if i6 is not None:
            vs=[v for v in range(N) if i6>>v&1]; s.add_clause([lit(a,b) for a,b in combinations(vs,2)]); 
            if rnd%200==0: print(f"  round {rnd}: still fixing alpha ({time.time()-t0:.0f}s, e={sum(bin(a).count('1') for a in adj)//2})",flush=True)
            continue
        c6=fc(adj,6)
        if c6 is not None:
            vs=[v for v in range(N) if c6>>v&1]; s.add_clause([-lit(a,b) for a,b in combinations(vs,2)]); continue
        e=sum(bin(a).count("1") for a in adj)//2
        print(f"SAT at E<={E}: found (alpha<=5, omega<=5) graph, edges={e}, rounds={rnd} => m*(no cap)<={e}<=120 => window SURVIVES",flush=True)
        json.dump({"n":N,"edges":e,"note":"alpha<=5,omega<=5 (no cap yet)","adj":[[adj[i]>>j&1 for j in range(N)] for i in range(N)]},
                  open(f"data/r6/candidates/ab_n31_nocap_E{e}.json","w"))
        return "SAT"
    print(f"TIMEOUT at E<={E} after {rnd} rounds",flush=True); return "TIMEOUT"

if __name__=="__main__":
    run(int(sys.argv[1]) if len(sys.argv)>1 else 120)
