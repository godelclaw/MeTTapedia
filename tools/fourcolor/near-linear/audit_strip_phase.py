#!/usr/bin/env python3
"""Replay a physical fixed-pair obstruction and a mixed-pair repair.

The phase lower bound, exterior disk planarity and physical reconstruction
are Lean theorems. Whole-graph sphere geometry, the shortest-history test
and complementary-pair batches remain independent program evidence.
"""
import argparse
from collections import defaultdict, deque
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import re

from audit_boundary_observation import components, proper, switch
from audit_component_detach import chain
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_independent_repair import complete_patch
from audit_strip_partial import partial


def geometry(faces, boundary):
    """Check a connected orientable triangular manifold with one boundary."""
    require(len({tuple(sorted(f)) for f in faces}) == len(faces), 'Duplicate face')
    inc = defaultdict(list)
    adj = defaultdict(set)
    for i, f in enumerate(faces):
        require(len(f) == len(set(f)) == 3, 'Degenerate face')
        for a,b in zip(f, f[1:] + f[:1]):
            inc[min(a,b),max(a,b)].append((i,a<b))
            adj[a].add(b);adj[b].add(a)
    ring = {tuple(sorted((a,b))) for a,b in zip(boundary,boundary[1:]+boundary[:1])}
    require(all(len(v) == (1 if e in ring else 2) for e,v in inc.items()), 'Face incidence')
    require(ring <= inc.keys(), 'Missing boundary edge')
    orient = {0:False};todo=[0]
    face_edges = [[tuple(sorted((a,b))) for a,b in zip(f,f[1:]+f[:1])] for f in faces]
    for i in todo:
        for e in face_edges[i]:
            if len(inc[e]) != 2:continue
            (j,d),(k,q)=inc[e]
            if k==i:j,k,d,q=k,j,q,d
            require(j==i,'Incidence mismatch')
            expected=orient[i]^(d==q)
            if k in orient:require(orient[k]==expected,'Nonorientable surface')
            else:orient[k]=expected;todo.append(k)
    require(len(orient)==len(faces),'Disconnected face complex')
    for v,ns in adj.items():
        link={w:set() for w in ns}
        for f in faces:
            if v in f:
                a,b=[w for w in f if w!=v];link[a].add(b);link[b].add(a)
        seen={next(iter(link))};todo=list(seen)
        for w in todo:
            for z in link[w]-seen:seen.add(z);todo.append(z)
        require(seen==set(link),'Disconnected vertex link')
        ds=sorted(map(len,link.values()))
        require(ds==([1,1]+[2]*(len(ds)-2) if v in boundary else [2]*len(ds)),
                'Nonmanifold vertex link')
    require(len(adj)-len(inc)+len(faces)==(1 if boundary else 2),'Wrong Euler characteristic')
    return dict(adj)


def verify(here):
    raw=(here/'D0099.conf').read_bytes()
    require(sha256(raw).hexdigest()=='932265e50ca2493734dc03f20b4259d6506e968b6cbd8bc16b48f9f53083ae82', 'Source pin differs')
    ring,source=graph(raw)
    fixture_path=here/'strip-phase-example.json';f=json.loads(fixture_path.read_text())
    colours=f['colouring'];ports=list(range(11));n=len(colours)
    require(ring==11 and n==23, 'Wrong carriers')
    adj=geometry(f['faces'],ports)
    c=dict(enumerate(colours));proper(adj,c)
    initial=partial(source,ring,colours[:ring],(0,5));require(initial is not None,'Two holes do not suffice')
    def needs_two(word):
        return all(partial(source,ring,word,omit) is None for k in (0,1)
                   for omit in combinations(range(8),k))
    require(needs_two(colours[:ring]),'Initial lower bound differs')
    phase=[];allwords=set()
    for a,b in combinations(range(4),2):
        blocks=[sorted(p) for p in components(adj,c,(a,b)) if p&set(ports)]
        words=set()
        for mask in range(1<<len(blocks)):
            word=list(colours[:ring])
            for i,block in enumerate(blocks):
                if mask>>i&1:
                    for v in block:
                        if v<ring:word[v]^=a^b
            require(needs_two(word),'A fixed-pair endpoint strictly improves')
            words.add(tuple(word))
        phase.append({'pair':[a,b],'visible_components':len(blocks),'boundary_endpoints':len(words),
                      'boundary_blocks':[[v for v in p if v<ring] for p in blocks]})
        allwords |= words
    complement_batches=[]
    for delta in (1,2,3):
        pairs=[(a,a^delta) for a in range(4) if a<a^delta]
        blocks=[p for pair in pairs for p in components(adj,c,pair) if p&set(ports)]
        for mask in range(1<<len(blocks)):
            word=list(colours[:ring])
            for j,block in enumerate(blocks):
                if mask>>j&1:
                    for v in block:
                        if v<ring:word[v]^=delta
            require(needs_two(word),'A complementary-pair batch improves')
        complement_batches.append({'xor_colour':delta,'component_subsets':1<<len(blocks),
                                   'every_result_needs_at_least_two_holes':True})
    states=[c];chains=[];stages=[2]
    for command in f['commands']:
        new,support=switch(adj,states[-1],command['pair'],command['root'])
        chains.append(chain(adj,support,command['root']));states.append(new)
        word=[new[v] for v in ports]
        stages.append(next(k for k in range(4) if any(partial(source,ring,word,omit) is not None
                      for omit in combinations(range(8),k))))
    completed=complete_patch(source,[states[-1][v] for v in ports]);require(completed is not None,'Repair fails')
    source_vertex=lambda v:v if v<11 else v+12
    source_faces=[list(t) for t in combinations(range(19),3)
                  if all(b in source[a] for a,b in combinations(t,2))]
    fullfaces=f['faces']+[[source_vertex(v) for v in t] for t in source_faces]
    full=geometry(fullfaces,[])
    require(len(full)==31,'Wrong whole graph')
    fullcolour=states[-1]|{23+i:completed[11+i] for i in range(8)};proper(full,fullcolour)
    for v in range(11,19):
        require(full[source_vertex(v)]=={source_vertex(w) for w in source[v]},'Core star differs')
    # Independently replay the literal graph, colours and physical chains used in Lean.
    lean=here.parents[2]/'lean/fourcolor-classical/MettapediaFourColor/StripPhaseObstruction.lean'
    text=lean.read_text()
    def definition(name):
        m=re.search(rf'^def {name}\b(.*?)(?=^(?:def |theorem |instance |private |/--|noncomputable |end ))',text,re.M|re.S)
        require(m is not None,f'Missing Lean definition {name}');return re.sub(r'\s+','',m[1])
    edges=sorted((a,b) for a,ns in adj.items() for b in ns if a<b)
    require(definition('exteriorEdges').split(':=',1)[1]=='['+','.join(f'({a},{b})' for a,b in edges)+']','Lean graph differs')
    for s,state in enumerate(states):
        row='!['+','.join('c'+str(state[v]) for v in range(n))+']'
        require(f'|{s}=>{row}' in definition('values'),'Lean colouring differs')
    list_text=lambda xs:'['+','.join(map(str,xs))+']'
    require(definition('repairChain').split(':=',1)[1]=='!'+list_text(map(list_text,chains)),'Lean switch supports differ')
    require(definition('finalCore').split(':=',1)[1]=='!['+','.join('c'+str(x)for x in completed[11:])+']','Lean reconstruction differs')
    # The shortest-history check concerns this literal exterior only.
    seen={tuple(colours)};front=[c];count=0
    for depth in range(2):
        nxt=[]
        for state in front:
            for pair in combinations(range(4),2):
                for support in components(adj,state,pair):
                    new,_=switch(adj,state,pair,min(support));key=tuple(new[v] for v in range(n))
                    if key in seen:continue
                    seen.add(key);nxt.append(new);count+=1
                    require(complete_patch(source,[new[v]for v in ports]) is None,'A shorter physical repair exists')
        front=nxt
    return {'classification':'PHYSICAL_PHASE_OBSTRUCTION_AND_MIXED_PAIR_RECONSTRUCTION',
            'source':'D0099.conf','source_sha256':sha256(raw).hexdigest(),
            'attribution':'Yuta Inoue D0099, MIT catalogue; Gonthier/Emery source semantics.',
            'fixture_sha256':sha256(fixture_path.read_bytes()).hexdigest(),
            'exterior':{'vertices':n,'edges':len(edges),'triangular_faces':len(f['faces']),
                        'one_simple_boundary':ring,'orientable_disk':True},
            'whole':{'vertices':len(full),'edges':sum(map(len,full.values()))//2,'triangular_faces':len(fullfaces),
                     'sphere':True,'minimum_degree':min(map(len,full.values())),
                     'complete_source_stars':True,'minimal_counterexample_geometry_claimed':False},
            'fixed_pair_phases':phase,'phase_endpoint_checks':sum(x['boundary_endpoints']for x in phase),
            'distinct_boundary_endpoints':len(allwords),'initial_minimum_holes':2,
            'program_complementary_pair_batches':complement_batches,
            'every_phase_minimum_holes_at_least':2,'repair':f['commands'],'repair_hole_counts':stages,
            'physical_switch_sizes':[len(set(x))for x in chains],
            'whole_colouring_reconstructed':True,'program_shortest_repair_length':3,
            'program_states_checked_at_distance_one_or_two':count,
            'scope':['The Lean phase theorem covers arbitrary phase length, including reversed and equal colour pairs.',
                     'StripPhaseDisk separately proves exterior planarity and Kempe closure in Lean.',
                     'Whole-graph spherical geometry, complementary-pair batches and shortest physical repair length are program checks.',
                     'No negative claim for all mixed-pair histories, degree-five minimal counterexamples or compact compositional proofs.',
                     'No geometric supply, strict ambient reduction or catalogue deletion is established.'],
            'verifier_sha256':sha256(Path(__file__).read_bytes()).hexdigest()}

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path);args=parser.parse_args()
    result=verify(Path(__file__).resolve().parent);payload=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(payload)
    print(payload,end='')
