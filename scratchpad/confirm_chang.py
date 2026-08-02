import sys, random; sys.path.insert(0,'.')
from collections import defaultdict
from probe_dir_flip import refine, cells, all_auts, orbits_of, t8_chang
from probe_dir_flip4 import scheme
C8=[tuple(sorted((i,(i+1)%8))) for i in range(8)]
n,adj=t8_chang(C8); aset=[set(a) for a in adj]
col=refine(n,adj,[0]*n)
auts=all_auts(n,adj,col); orb=orbits_of(n,auts)
print("Chang-2 n=%d |Aut|=%d root cells=%s orbit sizes=%s"%(
    n,len(auts),sorted(len(v) for v in cells(col).values()),
    sorted(defaultdict(int,{o:sum(1 for x in orb if x==o) for o in set(orb)}).values())))
print("orbit of 0 == orbit of 3 ?", orb[0]==orb[3])
for seed in (3,11,101):
    rng=random.Random(seed); tally=defaultdict(int); dep=defaultdict(int); mixd=defaultdict(int)
    bydir=defaultdict(lambda: defaultdict(int))
    for _ in range(1000):
        v,nm,dp=scheme(n,adj,col,0,3,rng,orb,aset)
        tally[v]+=1; dep[dp]+=1; mixd[nm]+=1; bydir[v][nm]+=1
    print(" seed%-4d %s  divDepth=%s  mixedPicksBefore=%s"%(
        seed,dict(sorted(tally.items())),dict(sorted(dep.items())),dict(sorted(mixd.items()))))
    for d in sorted(bydir): print("      %s -> mixedPicks %s"%(d,dict(sorted(bydir[d].items()))))
