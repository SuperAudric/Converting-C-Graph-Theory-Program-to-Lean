# De-risk: is the COORDINATE-FREE forced-reader (e_v in rowspace(H)?, forced value)
# (a) unconditionally equivariant under relabelling sigma, and
# (b) correct on a MIXED system (some coords rigid-forced, some gauge-free)?
# Pure F2 linear algebra. No frame, no uniqueness assumption.

def rref(rows, n):
    rows = [r[:] for r in rows]
    piv = []
    r = 0
    for c in range(n):
        pr = next((i for i in range(r,len(rows)) if rows[i][c]), None)
        if pr is None: continue
        rows[r], rows[pr] = rows[pr], rows[r]
        for i in range(len(rows)):
            if i!=r and rows[i][c]:
                rows[i] = [a^b for a,b in zip(rows[i],rows[r])]
        piv.append(c); r+=1
    return rows[:r], piv

def in_rowspace(rows, n, target):
    # solve for combo of rows == target over F2 by augmenting
    R,_ = rref([row[:]+[target[k]] for k,row in enumerate([target])]+[r[:]+[0] for r in rows], n+1)
    # simpler: check rank(rows) == rank(rows+[target])
    b0 = rref(rows, n)[1]
    b1 = rref(rows+[target], n)[1]
    return len(b0)==len(b1)

def forced_value(rows, n, b, v):
    # e_v: is it in rowspace? if so, forced value = combo applied to b.
    ev = [1 if k==v else 0 for k in range(n)]
    if not in_rowspace(rows, n, ev):
        return None  # free / gauge
    # find combo c (subset of rows, over F2) with XOR == ev; value = XOR of corresponding b
    # gaussian on augmented [rows | b] then express ev
    m = len(rows)
    aug = [rows[i][:]+[1 if j==i else 0 for j in range(m)] for i in range(m)]
    A,piv = rref(aug, n)  # reduce only first n cols
    # back-substitute ev in terms of pivots
    coeff = [0]*m
    target = ev[:]
    for row in A:
        lead = next((c for c in range(n) if row[c]), None)
        if lead is None: continue
        if target[lead]:
            target = [a^b for a,b in zip(target, row[:n])]
            for j in range(m):
                coeff[j]^=row[n+j]
    val = 0
    for j in range(m):
        if coeff[j]: val ^= b[j]
    return val

def reader(rows, n, b):
    return [forced_value(rows,n,b,v) for v in range(n)]

def transport_row(sigma, row, n):   # transportRow sigma: (r ∘ sigma^{-1})
    inv = [0]*n
    for i in range(n): inv[sigma[i]]=i
    return [row[inv[u]] for u in range(n)]

# ---- MIXED system: coord0 rigid-forced, coords1,2 coupled gauge, coord3 free ----
n=4
H=[[1,0,0,0],[0,1,1,0]]
b=[1,0]              # x0 forced to 1; check 0,1,2 couples 1+2=0
print("H:",H,"b:",b)
print("reader (None=free/gauge):", reader(H,n,b))
# expect: [1, None, None, None]  -> coord0 rigid (value1), rest free

# ---- equivariance under sigma = swap(0,3) ----
sigma=[3,1,2,0]
Hs=[transport_row(sigma,r,n) for r in H]
print("Hσ:",Hs)
rs=reader(Hs,n,b)
r0=reader(H,n,b)
inv=[0]*n
for i in range(n): inv[sigma[i]]=i
equiv = all(rs[v]==r0[inv[v]] for v in range(n))
print("reader(Hσ):",rs,"  reader(H)∘σ⁻¹:",[r0[inv[v]] for v in range(n)])
print("EQUIVARIANT:",equiv)

# ---- second sigma, and a second system ----
for sg in ([1,2,3,0],[2,0,3,1],[0,2,1,3]):
    Hs=[transport_row(sg,r,n) for r in H]
    invg=[0]*n
    for i in range(n): invg[sg[i]]=i
    ok=all(reader(Hs,n,b)[v]==r0[invg[v]] for v in range(n))
    print("sigma",sg,"equivariant:",ok)

# fully-rigid control: H spanning all e_i -> all forced
H2=[[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]]; b2=[1,0,1,1]
print("fully-rigid reader:", reader(H2,n,b2), "(expect all pinned)")
# pure-gauge control: one coupling, nothing pinned
H3=[[1,1,0,0]]; b3=[0]
print("pure-gauge reader:", reader(H3,n,b3), "(expect all None)")
