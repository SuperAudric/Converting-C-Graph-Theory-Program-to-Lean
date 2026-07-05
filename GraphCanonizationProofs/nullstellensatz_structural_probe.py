import itertools, collections

def make_Q(p, m, eps):
    d = 2*m
    squares = {(a*a) % p for a in range(p)}
    g = next(a for a in range(2,p) if a not in squares)
    def Q(x):
        s = 0
        for i in range(m):
            s += x[2*i]*x[2*i+1]
        if eps == -1:
            s -= x[d-2]*x[d-1]
            s += x[d-2]*x[d-2] - g*x[d-1]*x[d-1]
        return s % p
    return Q, d

def polar(Q,x,y,p):
    xy=[(x[i]+y[i])%p for i in range(len(x))]
    return (Q(xy)-Q(x)-Q(y))%p

def rank_modp(rows,p,ncol):
    A=[r[:] for r in rows]; r=0; nr=len(A)
    for c in range(ncol):
        piv=None
        for i in range(r,nr):
            if A[i][c]%p!=0: piv=i;break
        if piv is None: continue
        A[r],A[piv]=A[piv],A[r]
        inv=pow(A[r][c]%p,p-2,p)
        A[r]=[(x*inv)%p for x in A[r]]
        for i in range(nr):
            if i!=r and A[i][c]%p!=0:
                f=A[i][c]%p
                A[i]=[(A[i][k]-f*A[r][k])%p for k in range(ncol)]
        r+=1
        if r==nr: break
    return r

def deg2_vanish_dim(Q,d,p):
    # dimension of space of quadratic forms (homog deg2, dim = d + C(d,2)) vanishing on cone(Q).
    # monomials: x_i x_j (i<=j). Build matrix: rows=cone points, cols=monomials, entry=monomial(v).
    monos=[(i,j) for i in range(d) for j in range(i,d)]
    V=[list(v) for v in itertools.product(range(p),repeat=d)]
    cone=[v for v in V if Q(v)==0]  # include 0; homogeneous so fine
    rows=[]
    for v in cone:
        rows.append([ (v[i]*v[j])%p for (i,j) in monos])
    rk=rank_modp(rows,p,len(monos))
    return len(monos)-rk  # nullity = dim of vanishing forms

def test(p,m,eps):
    Q,d=make_Q(p,m,eps)
    V=[list(v) for v in itertools.product(range(p),repeat=d)]
    iso=[v for v in V if Q(v)==0 and any(c for c in v)]
    aniso=[v for v in V if Q(v)!=0]
    span_rank=rank_modp([v[:] for v in iso],p,d)
    # anisotropic connectivity under polar!=0
    A=aniso; adj=collections.defaultdict(list)
    for i in range(len(A)):
        for j in range(i+1,len(A)):
            if polar(Q,A[i],A[j],p)!=0: adj[i].append(j);adj[j].append(i)
    seen={0};st=[0]
    while st:
        u=st.pop()
        for w in adj[u]:
            if w not in seen: seen.add(w);st.append(w)
    conn=len(seen)==len(A)
    vd=deg2_vanish_dim(Q,d,p)
    print(f"  p={p} m={m} eps={eps:+d}: iso_span={span_rank}/{d}  aniso_Bconn={conn}  deg2_vanishDim={vd}  (want span=d, conn=True, vd=1)")

for (p,m,eps) in [(3,2,1),(3,2,-1),(5,2,1),(5,2,-1),(7,2,1),(7,2,-1),(3,3,1),(3,3,-1)]:
    test(p,m,eps)
