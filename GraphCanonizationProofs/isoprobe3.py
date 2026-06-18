from collections import defaultdict
from itertools import product
P=3
pts=list(product(range(P),repeat=4))
def sub(a,b): return tuple((a[i]-b[i])%P for i in range(4))
def Q(x): return (x[0]*x[1]+x[2]*x[2]+x[3]*x[3])%P     # VO^-_4(3)
def iso(w):
    if all(c==0 for c in w): return 0
    return 1 if Q(w)==0 else 2

def oneround_classes(T):
    # color u by histogram { (pattern to T, iso(z-u)) : z != u }
    key={}
    for u in pts:
        h=defaultdict(int)
        for z in pts:
            if z==u: continue
            pat=tuple(iso(sub(z,t)) for t in T)
            h[(pat,iso(sub(z,u)))]+=1
        key[u]=frozenset(h.items())
    classes=defaultdict(list)
    for u in pts: classes[key[u]].append(u)
    return classes

def is_discrete(T):
    c=oneround_classes(T)
    return all(len(v)==1 for v in c.values()), len(c)

frame=[(0,0,0,0),(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1)]
print("standard frame (size 5):", is_discrete(frame))

# greedy: start from {0}, add the point that maximizes #classes of the one-round partition
def ncls(T): return len(oneround_classes(T))
T=[(0,0,0,0)]
while True:
    d,nc=is_discrete(T)
    if d: break
    best=None;bestn=-1
    for p in pts:
        if p in T: continue
        n=ncls(T+[p])
        if n>bestn: bestn=n;best=p
    T=T+[best]
    if len(T)>12: break
print(f"greedy one-round base: size {len(T)}, T={T}, discrete={is_discrete(T)}")

# try standard frame + symmetry-breaking extra points (size 6)
for extra in [(0,0,1,1),(0,0,2,1),(1,1,1,0),(0,0,1,2),(1,0,1,0)]:
    print(f"frame+{extra} (size 6): {is_discrete(frame+[extra])}")
