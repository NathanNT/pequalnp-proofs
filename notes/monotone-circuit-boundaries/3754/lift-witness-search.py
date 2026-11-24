import json,networkx as nx
from pathlib import Path
from lift_search import solve
goals=[('P7',nx.path_graph(7),9),('C6-leaf',nx.Graph(list(nx.cycle_graph(6).edges())+[(0,6)]),9),
       ('C8',nx.cycle_graph(8),11),('theta333',nx.Graph([(0,1),(1,2),(2,7),(0,3),(3,4),(4,7),(0,5),(5,6),(6,7)]),12)]
records=[]
for name,g,upper in goals:
  for s in range(max(len(g)-1,upper-1),upper+1):
    stat,w=solve(g,s,True,35,witnesses=True)
    records.append({'name':name,'edges':list(g.edges),'size':s,'status':stat,'witness':w})
    print(name,s,stat,flush=True)
    Path('lift-witness-search.json').write_text(json.dumps(records,indent=1),encoding='utf8')
    if stat=='SAT':break
