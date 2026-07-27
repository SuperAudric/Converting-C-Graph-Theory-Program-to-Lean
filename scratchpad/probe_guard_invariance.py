"""Is `Certified` (deepen's own harvest, transitive on the branch cell) RELABELLING-INVARIANT?
That is the §10/§17.4 open item.  If the harvest's block partition is labelling-dependent anywhere,
the target is dead and an alternate (equivariant-supply) guard is required."""
import sys, random; sys.path.insert(0,'/workspace/scratchpad')
import probe_orbit_oracle as P, probe_polyloop as Q
from collections import defaultdict

def relabel(n, adj, s):
    out=[[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(n): out[s[i]][s[j]]=adj[i][j]
    return out

def transport(n, col, s):
    out=[0]*n
    for u in range(n): out[s[u]]=col[u]
    return out

def harvest_blocks(n, adj, col):
    """All-anchor harvest, group-closed, restricted to the branch cell."""
    cid,C=P.target_cell(n,col)
    if cid is None: return None
    firsts={r:P.refine(n,adj,P.indiv(n,col,r)) for r in C}
    par={v:v for v in C}
    def f(x):
        while par[x]!=x: par[x]=par[par[x]]; x=par[x]
        return x
    gens=[]
    for a in C:
        for rj,t in P.harvest_from(n,adj,col,a,firsts).items():
            if t is not None:
                gens.append(t); ra,rb=f(a),f(rj)
                if ra!=rb: par[ra]=rb
    ch=True
    while ch:
        ch=False
        for g in gens:
            for v in C:
                if f(v)!=f(g[v]): par[f(v)]=f(g[v]); ch=True
    d=defaultdict(set)
    for v in C: d[f(v)].add(v)
    return frozenset(frozenset(b) for b in d.values())

def check(name, n, adj, colf, trials=6, seed=1):
    """colf(n,adj) -> the node colouring, computed INVARIANTLY on whatever graph it is given."""
    col=colf(n,adj)
    base=harvest_blocks(n,adj,col)
    if base is None: print(f'{name}: discrete'); return
    tb=P.orbit_partition(n,adj,col,sorted(set().union(*base)))
    norb=len(set(tb.values())) if tb else -1
    rnd=random.Random(seed); ok=True; seen=set()
    for _ in range(trials):
        s=list(range(n)); rnd.shuffle(s)
        a2=relabel(n,adj,s)
        col2=colf(n,a2)                    # recomputed invariantly on the relabelled graph
        b2=harvest_blocks(n,a2,col2)
        img=frozenset(frozenset(s[v] for v in blk) for blk in base)
        seen.add(tuple(sorted(len(b) for b in b2)))
        if b2!=img: ok=False
    print(f'{name:38s} |blocks|={len(base)} true-orbits={norb}  '
          f'partition transports under {trials} relabellings = {ok}   '
          f'block-size profiles seen: {sorted(seen)}')

def root_col(n,adj): return P.refine(n,adj,[0]*n)

def cfi_stall_col(n,adj):
    adjl=Q.adjlist(n,adj); col=Q.refine(n,adjl,[0]*n)
    for _ in range(n+2):
        cid,C=Q.target_cell(n,col)
        if cid is None: return col
        ks={v:Q.rref_key(n,adj,adjl,col,v) for v in C}
        if len(set(ks.values()))>1:
            sig=[(col[u],ks.get(u,())) for u in range(n)]
            rank={t:i for i,t in enumerate(sorted(set(sig)))}
            col=Q.refine(n,adjl,[rank[sig[u]] for u in range(n)]); continue
        return col
    return col

print("Is the deepen harvest's branch-cell partition RELABELLING-INVARIANT?\n")
es=Q.cubic(8,19)
n,adj=Q.build_cfi_base(es,8,False)
check('CFI cubic m=8 pl @ the |C|=16 node', n, adj, cfi_stall_col, trials=6)
for w in ('A','B'):
    n,adj=P.chang(w); check(f'Chang-{w} root', n, adj, root_col, trials=6)
n,adj=P.build_mp(P.MIXED); check('MIXED multipede root', n, adj, root_col, trials=6)
n,adj=P.disjoint([P.cycle(3),P.cycle(4),P.cycle(5)]); check('C3+C4+C5 root', n, adj, root_col, trials=6)
