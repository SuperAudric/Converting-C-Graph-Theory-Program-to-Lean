# Double-check: can refineByFrame (ONE forced F2 bit per vertex) discretize a
# RIGID cell (zero symmetry) with >2 same-coloured vertices?
# Rigid = trivial kernel = unique solution x0. forcedVal v = some(x0 v) for ALL v.
# refineByFrame v = 3*chi_v + encOpt(some(x0 v))  -- encOpt(some 0)=1, encOpt(some 1)=2.

def rref(rows, n):
    rows=[r[:] for r in rows]; piv=[]; r=0
    for c in range(n):
        pr=next((i for i in range(r,len(rows)) if rows[i][c]),None)
        if pr is None: continue
        rows[r],rows[pr]=rows[pr],rows[r]
        for i in range(len(rows)):
            if i!=r and rows[i][c]: rows[i]=[a^b for a,b in zip(rows[i],rows[r])]
        piv.append(c); r+=1
    return rows[:r],piv

# A RIGID system on n=4 vertices, all the SAME colour (one cell of size 4).
# H = full-rank => unique solution, trivial kernel (rigid, zero symmetry).
n=4
H=[[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]]   # identity => rank 4, trivial kernel
b=[1,0,0,1]                                     # unique solution x0 = b
x0=b
# every e_v in rowspace (full) => all forced
def encOpt_singlebit(v): return 1+x0[v]         # some(x0 v): 0->1, 1->2
refined_single=[encOpt_singlebit(v) for v in range(n)]   # chi same for all -> compare just the digit
print("SINGLE-BIT reader refined digits:", refined_single)
print("  distinct?", len(set(refined_single))==n, " (need", n, "distinct to discretize)")

# RICHER reader: each vertex's COLUMN in the canonical RREF (its full forced signature).
R,piv=rref(H,n)
# column c signature = tuple of R[i][c] over pivot rows
def col_sig(c): return tuple(R[i][c] for i in range(len(R)))
refined_rich=[col_sig(v) for v in range(n)]
print("RICHER (RREF-column) reader:", refined_rich)
print("  distinct?", len(set(refined_rich))==n)

# A less trivial rigid system (not identity) with a 3-cell collision under single bit:
H2=[[1,1,0],[0,1,1],[1,0,1]]   # rank? 
R2,p2=rref(H2,3); print("\nH2 rank",len(p2),"(3=rigid)")
# solve H2 x = b2
import itertools
def solve(H,b,n):
    for x in itertools.product([0,1],repeat=n):
        if all(sum(H[i][j]*x[j] for j in range(n))%2==b[i] for i in range(len(H))): 
            yield x
b2=[1,0,1]; sols=list(solve(H2,b2,3)); print("solutions:",sols,"(unique=rigid)" if len(sols)==1 else "(NOT unique)")
x0b=sols[0]; print("single-bit digits:",[1+x0b[v] for v in range(3)],"distinct?",len(set(x0b))==3)
print("RREF-col sigs:",[tuple(R2[i][c] for i in range(len(R2))) for c in range(3)])
