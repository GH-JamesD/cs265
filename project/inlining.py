import json
import sys
import random
import string
import networkx as nx
from inlining_tree import *
from collections import defaultdict, OrderedDict, deque

def get_call_graph(prog, ignore_recursive = True):
    call_graph = defaultdict(set)
    for fn in prog["functions"]:
        for inst in fn["instrs"]:
            if "op" in inst and inst["op"] == "call":
                for func in inst["funcs"]:
                    # For now, we ignore recursive calls
                    if ignore_recursive and func == fn["name"]:
                        continue
                    else:
                        call_graph[fn["name"]].add(func)
    return nx.DiGraph(call_graph)




if __name__ == "__main__":
    prog = json.load(sys.stdin)
    call_graph = get_call_graph(prog)
    plot_call_graph(call_graph)
    inlining_tree = build_inlining_tree(call_graph)
    plot_inlining_tree(inlining_tree)



    #for fn in prog["functions"]:


    # print(states)
    #json.dump(prog, sys.stdout, indent=2)