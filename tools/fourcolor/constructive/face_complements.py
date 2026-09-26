"""Support density of every face complement in small normal-form spheres.

For each face of length at most 11 whose complement is connected, the
complement is a piece whose ports are the face's spokes; the density of its
support among the parity-admissible spoke words is reported, grouped by face
length.  Maps: the barrels (four cyclic rows of k vertices: two k-gons and 2k
pentagons), the closed double caps (two k-gon-plus-pentagon-ring discs glued
with opposite orientations) and C60.  Uses piece_support via sphere_cut.

Usage: python3 face_complements.py
"""
import sys, networkx as nx
from sphere_cut import support_reps, side_piece, truncate
def faces_of(G):
    ok, emb = nx.check_planarity(G); assert ok
    seen=set(); faces=[]
    for u,v in emb.edges():
        if (u,v) in seen: continue
        f=emb.traverse_face(u,v,mark_half_edges=seen)
        faces.append(f)
    return faces
def barrel(k):
    G=nx.Graph()
    for i in range(k):
        j=(i+1)%k
        G.add_edge(('r0',i),('r0',j)); G.add_edge(('r3',i),('r3',j))
        G.add_edge(('r0',i),('r1',i)); G.add_edge(('r2',i),('r3',i))
        G.add_edge(('r1',i),('r2',i)); G.add_edge(('r1',j),('r2',i))
    return G
def double_cap(k):
    G=nx.Graph()
    for s in (0,1):
        for i in range(k):
            j=(i+1)%k
            G.add_edge((s,'c',i),(s,'c',j)); G.add_edge((s,'c',i),(s,'in',i))
            G.add_edge((s,'in',i),(s,'out',i)); G.add_edge((s,'in',j),(s,'out',i))
    for i in range(k):
        G.add_edge((0,'out',i),(1,'out',(-i)%k))
    return G
def run(name,G):
    assert all(d==3 for _,d in G.degree()), name
    stats={}
    for f in faces_of(G):
        F=set(f); Y=set(G)-F
        cut=[(u,v) for u,v in G.edges() if (u in F)!=(v in F)]
        if len(cut)>11 or not nx.is_connected(G.subgraph(Y)): continue
        n,e,p=side_piece(G,Y,cut)
        adm,s,_=support_reps(n,e,p)
        stats.setdefault(len(f),[]).append(s/adm)
    summ=", ".join(f"{L}-gons: min {min(v):.3f} max {max(v):.3f} ({len(v)})" for L,v in sorted(stats.items()))
    print(f"{name} (V={G.number_of_nodes()}): complement density by face length: {summ}", flush=True)
if __name__ == "__main__":
    for k in range(5,11): run(f"barrel k={k}", barrel(k))
    for k in range(5,9): run(f"double cap k={k}", double_cap(k))
    run("C60", nx.convert_node_labels_to_integers(truncate(nx.icosahedral_graph())))
