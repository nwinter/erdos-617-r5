import sys; from importlib import import_module
sys.path.insert(0,'r6'); R=import_module('recompute2'); from math import comb
for r,sat in ((5,R.r5_sat),(6,R.r6_sat)):
    S=R.S_size(r); P=R.P_table(r,r-1,S,sat=sat)
    print(f"\nr={r}, S={S}: P-ladder (P2=alpha<=2 base ... P{r-1}=e(H))")
    for a in range(2,r):
        vals={q:('none' if P[a][q]==R.INF else P[a][q]) for q in range(max(6,S-8),S+1)}
        print(f"  P_{a}: {vals}")
    # r=5 'L-table' is P_3; r=6 analogue is P_3 too (alpha<=3 level)
