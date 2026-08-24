import time
exec(open('switching_rulers2.py').read().split("t0 = time.time()")[0])
import networkx as nx
rook = nx.convert_node_labels_to_integers(
    nx.cartesian_product(nx.complete_graph(4), nx.complete_graph(4)))
S = slots(16); rm = mask_of(rook, 16)
t = time.time(); k = 0; iso = {}
for c in cut_vectors(16):
    if wl2_discrete(rm ^ c, 16, S): k += 1
print(f"EXHAUSTIVE n=16 rook(4,4) switching class: 2-WL-discrete members = {k}/32768  [{time.time()-t:.0f}s]")
