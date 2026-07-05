import itertools, collections
def make_Q(p,m,eps):
    d=2*m; sq={(a*a)%p for a in range(p)}; g=next(a for a in range(2,p) if a not in sq)
    def Q(x):
        s=0
        for i in range(m): s+=x[2*i]*x[2*i+1]
        if eps==-1:
            s-=x[d-2]*x[d-1]; s+=x[d-2]*x[d-2]-g*x[d-1]*x[d-1]
        return s%p
    return Q,d
def polar(Q,x,y,p):
    xy=[(x[i]+y[i])%p for i in range(len(x))]; return (Q(xy)-Q(x)-Q(y))%p
def rank_modp(rows,p,nc):
    A=[r[:] for r in rows]; r=0; nr=len(A)
    for c in range(nc):
        piv=next((i for i in range(r,nr) if A[i][c]%p),None)
        if piv is None: continue
        A[r],A[piv]=A[piv],A[r]; inv=pow(A[r][c]%p,p-2,p); A[r]=[(x*inv)%p for x in A[r]]
        for i in range(nr):
            if i!=r and A[i][c]%p: f=A[i][c]%p; A[i]=[(A[i][k]-f*A[r][k])%p for k in range(nc)]
        r+=1
        if r==nr: break
    return r
def test(p,m,eps):
    Q,d=make_Q(p,m,eps); V=[list(v) for v in itertools.product(range(p),repeat=d)]
    iso=[v for v in V if Q(v)==0 and any(v)]; aniso=[v for v in V if Q(v)!=0]
    # (1) punctured isotropic cone spans, for EVERY anisotropic y ?
    worst=d
    for y in aniso:
        punct=[x for x in iso if polar(Q,x,y,p)!=0]
        rk=rank_modp([x[:] for x in punct],p,d)
        worst=min(worst,rk)
    # (2) anisotropic graph diameter under polar!=0
    A=aniso; idx={tuple(v):i for i,v in enumerate(A)}; adj=collections.defaultdict(set)
    for i in range(len(A)):
        for j in range(i+1,len(A)):
            if polar(Q,A[i],A[j],p)!=0: adj[i].add(j); adj[j].add(i)
    # diameter via BFS from a few sources (full is heavy); check max over all sources of ecc, but sample
    def ecc(s):
        dist={s:0}; dq=collections.deque([s])
        while dq:
            u=dq.popleft()
            for w in adj[u]:
                if w not in dist: dist[w]=dist[u]+1; dq.append(w)
        return max(dist.values()) if len(dist)==len(A) else 999
    diam=max(ecc(s) for s in range(min(len(A),30)))
    print(f"  p={p} m={m} eps={eps:+d}: punctured_iso_span(worst y)={worst}/{d}  aniso_graph_diam(sampled)={diam}")
for (p,m,eps) in [(3,2,1),(3,2,-1),(5,2,1),(5,2,-1),(7,2,1),(7,2,-1),(3,3,1),(3,3,-1)]:
    test(p,m,eps)
