"""
(I)  Confirm the (4,4,4,4,4) variant iso-count via degree sequences + labelg.
(II) Validate KP's equality classification METHOD on small enumerable cases:
     max-size G_{n,r} graphs (K_{r+1}-free, chi>r) == the G(opt-seq) constructions.
     Uses nauty geng + labelg canonical forms.
"""
import itertools, subprocess
from collections import Counter
LABELG="/opt/homebrew/bin/labelg"; GENG="/opt/homebrew/bin/geng"

def g6_of(adj,n):
    bits=[]
    for j in range(1,n):
        for i in range(j): bits.append(1 if adj[i][j] else 0)
    out=chr(n+63)
    for i in range(0,len(bits),6):
        b=0
        for k in range(6): b=(b<<1)|(bits[i+k] if i+k<len(bits) else 0)
        out+=chr(b+63)
    return out
def canon(adj,n):
    return subprocess.run([LABELG],input=g6_of(adj,n)+"\n",capture_output=True,text=True).stdout.strip()
def build(seq,sizeA):
    n=sum(seq)+1; parts=[]; idx=0
    for sz in seq: parts.append(list(range(idx,idx+sz))); idx+=sz
    big=[i for i,a in enumerate(seq) if a>1]; s,t=sorted(big,key=lambda i:seq[i])[:2]
    S=[i for i in range(len(seq)) if i not in (s,t)]; Ns=parts[s]; y=parts[t][0]; Astar=Ns[:sizeA]
    adj=[[False]*n for _ in range(n)]
    def se(a,b,v): adj[a][b]=v; adj[b][a]=v
    partof={}
    for i,p in enumerate(parts):
        for v in p: partof[v]=i
    for a in range(n-1):
        for b in range(a+1,n-1):
            if partof[a]!=partof[b]: se(a,b,True)
    for v in set(v for i in S for v in parts[i])|{y}|set(Astar): se(n-1,v,True)
    for a in Astar: se(y,a,False)
    return n,adj,seq[s]
def degseq(adj,n): return tuple(sorted(sum(adj[v]) for v in range(n)))

print("=== (I) (4,4,4,4,4) variants ===")
cs={}
for sa in [1,2,3]:
    n,adj,ns=build((4,4,4,4,4),sa)
    cs[sa]=canon(adj,n)
    print(f" |A|={sa}: degseq={degseq(adj,n)}  canon={cs[sa][:20]}")
print(f" |A|=1 iso |A|=3 : {cs[1]==cs[3]};  |A|=2 distinct: {cs[2]!=cs[1]};  #iso classes = {len(set(cs.values()))}")

# ---- (II) small-case classification ----
def parse(line):
    d=[ord(c)-63 for c in line.strip()]; n=d[0]; bits=[]
    for b in d[1:]:
        for k in range(5,-1,-1): bits.append((b>>k)&1)
    A=[[False]*n for _ in range(n)]; idx=0
    for j in range(1,n):
        for i in range(j):
            if idx<len(bits) and bits[idx]: A[i][j]=A[j][i]=True
            idx+=1
    return n,A
def chi_le(A,n,k):
    col={}
    def bt(i):
        if i==n: return True
        used={col[u] for u in range(i) if A[i][u]}
        for c in range(k):
            if c not in used:
                col[i]=c
                if bt(i+1): return True
                del col[i]
        return False
    return bt(0)
def hasK(A,n,k): return any(all(A[a][b] for a,b in itertools.combinations(S,2)) for S in itertools.combinations(range(n),k))
def turan(n,r):
    q,s=divmod(n,r); return (n*n-(s*(q+1)**2+(r-s)*q**2))//2
def kps(n,r): return (n//r-1) if 2*r+1<=n else 2
def opt_seqs(n,r):
    # sequences sum=n-1, r parts nondecr, >=2 parts>1, maximising e(G(seq))
    def rec(t,k,lo):
        if k==1:
            if t>=lo: yield (t,)
            return
        for f in range(lo,t//k+1):
            for rr in rec(t-f,k-1,f): yield (f,)+rr
    def sig2(s):
        S=sum(s); return (S*S-sum(a*a for a in s))//2
    def eG(seq):
        big=[a for a in seq if a>1]
        if len(big)<2: return None
        ns,nt=sorted(big)[:2]; return sig2(seq)+sum(seq)-ns-nt+1
    best=-1; L=[]
    for seq in rec(n-1,r,1):
        if sum(1 for a in seq if a>1)<2: continue
        e=eG(seq)
        if e>best: best=e; L=[seq]
        elif e==best: L.append(seq)
    return best,L

def construction_canons(n,r):
    _,seqs=opt_seqs(n,r); cs=set()
    for seq in seqs:
        for sa in range(1, max(seq)):
            _,adj,ns=build(seq,sa)
            if sa>=ns: continue
            cs.add(canon(adj,n))
    return cs

print("\n=== (II) max-size G_{n,r} extremal graphs vs constructions ===")
for (n,r) in [(7,3),(8,3),(9,3),(8,4),(9,4)]:
    pr=turan(n,r)-kps(n,r)
    # enumerate all graphs, keep K_{r+1}-free, chi>r, e==pr; canon-dedup
    ext=set()
    proc=subprocess.Popen([GENG,str(n)],stdout=subprocess.PIPE,text=True,stderr=subprocess.DEVNULL)
    for line in proc.stdout:
        if not line.strip(): continue
        nn,A=parse(line)
        if sum(sum(r_) for r_ in A)//2 != pr: continue
        if hasK(A,n,r+1): continue
        if chi_le(A,n,r): continue
        ext.add(canon(A,n))
    proc.wait()
    con=construction_canons(n,r)
    print(f" (n,r)=({n},{r}) p_r={pr}: #extremal iso classes={len(ext)}  #construction iso classes={len(con)}  MATCH={ext==con}")
    if ext!=con:
        print(f"    extremal-only: {len(ext-con)}   construction-only: {len(con-ext)}")
