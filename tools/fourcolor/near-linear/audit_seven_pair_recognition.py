#!/usr/bin/env python3
"""Check rooted facial development against two independently built spheres.

This is a program check of the constructive recognition data, not a proof
that every relevant flat pair passes the degree test.
"""
from hashlib import sha256
import json
from pathlib import Path
import re

from audit_diamond_sources import require
from probe_flat_pairs import geometry


def verify(here):
    root = here.parents[2]
    source = root / 'lean/fourcolor-classical/MettapediaFourColor/SevenPairSectorRecognition.lean'
    raw = source.read_bytes()
    text = raw.decode()
    data = (source.parent / 'SevenPairSectorData.lean').read_text()
    words = json.loads(re.search(r'def faceBytes : ByteArray := ("[^"]+")', data)[1])
    decoded = [ord(c) - 65 for c in words]
    faces = [tuple(decoded[i:i+3]) for i in range(0,len(decoded),3)]
    domain = json.loads((here/'seven-pair-sector-audit.json').read_text())['fixed_degrees']
    domain = {int(k):v for k,v in domain.items()}
    opened = set(map(int,re.search(r'def openFaces .*?\{([^}]+)\}',text)[1].split(',')))
    steps = [tuple(map(int,m)) for m in re.findall(
        r'let v(\d+) := extend rotation v(\d+) v(\d+)',text)]
    require(len(steps)==22 and {c for c,_,_ in steps}==set(range(2,24)),
            'The development must construct exactly 22 further labels')
    require(len(opened)==23 and len(faces)==31, 'The seam partition differs')
    fixture = json.loads((here/'seven-pair-sector-example.json').read_text())
    ring = list(range(2,9))
    bipyramid = [f for a,b in zip(ring,ring[1:]+ring[:1])
                 for f in [(0,a,b),(1,b,a)]]
    results = []
    for name,triangles in [('sector_sphere',fixture['faces']),('seven_bipyramid',bipyramid)]:
        darts,ns,fw,_ = geometry(triangles)
        tested,matched,aliased = 0,0,0
        matches = []
        for a,b in sorted(darts):
            if len(ns[a])!=7:
                continue
            image={0:a,1:b}
            for c,u,v in steps:
                require(u in image and v in image and c not in image,
                        'An attachment uses an unavailable label')
                require((image[u],image[v]) in darts, 'An attachment lacks an actual edge')
                image[c]=fw[image[u],image[v]]
            for index in opened:
                u,v,w=faces[index]
                require(fw[image[u],image[v]]==image[w], 'An attached face is incorrect')
            tested+=1
            aliased+=len(set(image.values()))<24
            fits=all(len(ns[image[i]])==degree for i,degree in domain.items())
            if fits:
                for u,v,w in faces:
                    require(fw[image[u],image[v]]==image[w], 'A degree-closed seam fails')
                matched+=1
                matches.append([a,b])
                if (name,a,b)==('sector_sphere',0,1):
                    require(all(image[i]==i for i in range(24)), 'The retained chart changed')
        require(tested>0, 'No degree-seven root was tested')
        results.append({'example':name,'vertices':len(ns),'faces':len(triangles),
                        'degree_seven_rooted_edges':tested,'degree_test_passes':matched,
                        'roots_with_identified_labels':aliased,'matching_roots':matches})
    require([0,1] in results[0]['matching_roots'], 'The existing chart is no longer recognized')
    require(results[1]['roots_with_identified_labels']==results[1]['degree_seven_rooted_edges'],
            'The small sphere must exercise identified labels')
    require(results[1]['degree_test_passes']==0, 'The bipyramid should fail the retained degrees')
    return {'evidence':'Independent program checks; recognition coverage remains open.',
            'source_sha256':sha256(raw).hexdigest(),'root_labels':2,
            'triangle_attachments':22,'root_degree_closures':1,'remaining_degree_closures':8,
            'caller_supplied_facial_correspondences':0,'degree_observations':len(domain),
            'examples':results}


if __name__=='__main__':
    here=Path(__file__).resolve().parent
    result=verify(here)
    (here/'seven-pair-recognition-audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
