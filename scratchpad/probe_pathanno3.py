"""How far must the path object run to reach the orbitals on CFI? And does it ever
beat 2-WL there?  Continues probe_pathanno2.py to longer maxlen on the n=28 objects."""
import sys, time
from probe_pathcondense import (net_z4, rank_partition, npairclasses, same, finer_or_equal,
                                orbital_partition, wl2_pair_closure)
from probe_pathanno import simple_paths_profiles
from probe_cao_cleanroom import cfi, all_isos

def run(label, n, adj, maxlens):
    auts = all_isos(n, adj, [0]*n, [0]*n)
    Porb = orbital_partition(n, auts); P2wl = wl2_pair_closure(n, adj)
    print(f'=== {label} n={n} |Aut|={len(auts)} orbitals={npairclasses(Porb)} '
          f'2-WL={npairclasses(P2wl)} (2-WL==orb? {same(P2wl,Porb)})'); sys.stdout.flush()
    for L in maxlens:
        t0=time.time()
        try: A1,A2 = simple_paths_profiles(n,adj,L,deadline=t0+2400)
        except (TimeoutError,RecursionError) as e:
            print(f'    maxlen={L:2d} SKIPPED {type(e).__name__}'); continue
        print(f'    maxlen={L:2d}  A1={npairclasses(A1):3d}  A2={npairclasses(A2):3d}   '
              f'A2==orb? {str(same(A2,Porb)):5s}  orb refines A2? {finer_or_equal(Porb,A2):}   '
              f'A2 vs 2-WL: A2 refines 2WL? {finer_or_equal(A2,P2wl)}  '
              f'2WL refines A2? {finer_or_equal(P2wl,A2)}   [{time.time()-t0:.1f}s]')
        sys.stdout.flush()

if __name__ == '__main__':
    n,adj = net_z4(); run('net(Z4)=CFI[K4]-tw', n, adj, [14,16,18])
    K4=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
    n,adj,_,_ = cfi(K4,4,()); run('CFI[K4] plain', n, adj, [14,16,18])
