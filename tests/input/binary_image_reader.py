"""Independent binary-image comparison adapter, not an acceptance gate.

The Lean reader checks every row/edge again and owns semantic validation."""
from decimal import Decimal
import json
from pathlib import Path
import sys

MAGIC=b'LMIRIMG\x01'
class Number:
    def __init__(self,text):
        value=json.loads(text,parse_float=Decimal,parse_constant=lambda value: (_ for _ in ()).throw(ValueError(value)))
        if type(value) not in (int,Decimal):raise ValueError('number leaf')
        self.text=text
    def __eq__(self,other):return isinstance(other,Number) and self.text==other.text
    def __repr__(self):return f'Number({self.text!r})'
class Reader:
    def __init__(self,data):self.data=data;self.at=0
    def byte(self):
        if self.at>=len(self.data):raise ValueError('truncated')
        value=self.data[self.at];self.at+=1;return value
    def var(self):
        value=0
        for i in range(10):
            byte=self.byte()
            if i==9 and byte>1:raise ValueError('overflow')
            value|=(byte&127)<<(7*i)
            if byte<128:
                if i and byte==0:raise ValueError('noncanonical')
                return value
        raise ValueError('overflow')
    def count(self):
        count=self.var()
        if count>len(self.data)-self.at:raise ValueError('count')
        return count
    def text(self):
        size=self.count();value=self.data[self.at:self.at+size].decode('utf-8');self.at+=size;return value

def decode(data):
    if not data.startswith(MAGIC):raise ValueError('magic')
    r=Reader(data);r.at=len(MAGIC)
    fields=[r.text() for _ in range(r.count())]
    if len(set(fields))!=len(fields):raise ValueError('duplicate field')
    rows=[]
    for index in range(r.count()):
        tag=r.byte()
        if tag in (0,1,2):row=[tag]
        elif tag==3:row=[3,Number(r.text())]
        elif tag==4:row=[4,r.text()]
        elif tag in (7,8):
            value=r.var()
            if tag==8:
                if not 0<value<=2**63:raise ValueError('negative')
                value=-value
            row=[3,Number(str(value))]
        elif tag==5:
            edges=[r.var() for _ in range(r.count())]
            if any(edge>=index for edge in edges):raise ValueError('edge')
            row=[5,edges]
        elif tag==6:
            pairs=[];old=None
            for _ in range(r.count()):
                field=r.var()
                if field>=len(fields):raise ValueError('field')
                name=fields[field]
                if old is not None and old>=name:raise ValueError('order')
                if name=='$lean_miri_shared_ref':raise ValueError('reserved')
                old=name;edge=r.var()
                if edge>=index:raise ValueError('edge')
                pairs.append([field,edge])
            row=[6,pairs]
        else:raise ValueError('tag')
        rows.append(row)
    root=r.var()
    if r.at!=len(data):raise ValueError('trailing')
    if root>=len(rows) or rows[root][0]!=6:raise ValueError('root')
    if any(fields[field]=='shared_payloads' for field,_ in rows[root][1]):raise ValueError('catalog')
    return fields,rows,root

def json_wire(image):
    fields,rows,root=image
    parts=[]
    for row in rows:
        if row[0]==3:parts.append('[3,'+row[1].text+']')
        else:parts.append(json.dumps(row,ensure_ascii=False,separators=(',',':')))
    return ('{"fields":'+json.dumps(fields,ensure_ascii=False,separators=(',',':'))+
        ',"nodes":['+','.join(parts)+'],"root":'+str(root)+
        ',"schema":"lean-miri-prepared-image","schema_version":1}')

if __name__=='__main__':
    if sys.argv[1:2]==['--compare']:
        reference,source=map(Path,sys.argv[2:])
        expected=json.loads(reference.read_text(),parse_float=Number,parse_int=Number)
        actual=json.loads(json_wire(decode(source.read_bytes())),parse_float=Number,parse_int=Number)
        if actual!=expected:raise ValueError('binary image differs, including numeric wire spelling')
        print('typed JSON and binary rows match, including numeric wire spelling')
    else:
        source,destination=map(Path,sys.argv[1:]);image=decode(source.read_bytes())
        destination.write_text(json_wire(image))
        print('fields',len(image[0]),'nodes',len(image[1]),'root',image[2])
