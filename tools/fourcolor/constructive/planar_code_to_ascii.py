"""Convert planar code (as written by fullgen "code 1" or plantri) to plantri
ASCII code: one map per line, "n adj,adj,...", vertices named by consecutive
characters starting at 'a' (bytes above 127 for large maps), adjacency lists
in the stored cyclic order.  Only the one-byte variant (n <= 158) is supported.

Usage: python3 planar_code_to_ascii.py FILE > maps.txt
"""
import sys
data=open(sys.argv[1],'rb').read()
hdr=b'>>planar_code le<<'
if data.startswith(hdr): data=data[len(hdr):]
i=0; out=sys.stdout.buffer
while i < len(data):
    n=data[i]; i+=1
    if n==0: raise SystemExit("unsigned short format not supported")
    lists=[]
    for v in range(n):
        nb=[]
        while data[i]!=0:
            nb.append(data[i]-1); i+=1
        i+=1
        lists.append(bytes(97+u for u in nb))
    out.write(str(n).encode()+b' '+b','.join(lists)+b'\n')
