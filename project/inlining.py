import json
import sys
import random
import string
import networkx as nx
from inlining_tree import *
from collections import defaultdict, OrderedDict, deque
import os
import subprocess

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


def clean_inlining_order(order):
    cleaned_order = []
    for edge in order:
        cleaned_order.append((edge[0].split(":")[0], edge[1].split(":")[0]))
    return cleaned_order

def evaluate_inlining_tree(tree, prog):
    result_map = defaultdict(int)
    def evaluate(tree):
        if isinstance(tree, InliningTreeLeaf):
            cleaned = tuple(clean_inlining_order(tree.inlined_edges))
            if cleaned not in result_map:
                result_map[cleaned] = implement_compile_measure(cleaned, prog)
        elif isinstance(tree, InliningTreeBinaryNode):
            if tree.left:
                evaluate(tree.left)
            if tree.right:
                evaluate(tree.right)
        elif isinstance(tree, InliningTreeComponentsNode):
            for component in tree.components:
                evaluate(component)
    evaluate(tree)

def implement_inlining(inlined_edges, prog):
    # TODO: Implement inlining
    return prog


def implement_compile_measure(inlined_edges, prog):
    implemented_prog = implement_inlining(inlined_edges, prog)
    
    temp_json_file = "temp.bril.json"
    with open(temp_json_file, "w") as f:
        json.dump(implemented_prog, f, indent=2)

    try:
        brilift_output = "bril.o"
        subprocess.run(f"brilift -o bril.o -O none < {temp_json_file}", shell=True, check=True)

        rt_location = "../../bril/brilift/rt.o"

        executable = "myprog"
        subprocess.run(["cc", brilift_output, rt_location, "-o", executable], check=True)

        binary_size = os.path.getsize(executable)

        return binary_size
    finally:
        if os.path.exists(temp_json_file):
            os.remove(temp_json_file)
        if os.path.exists(brilift_output):
            os.remove(brilift_output)
        if os.path.exists(executable):
            os.remove(executable)



if __name__ == "__main__":
    prog = json.load(sys.stdin)
    bin_size = implement_compile_measure([], prog)
    print(bin_size)
    #call_graph = get_call_graph(prog)
    #plot_call_graph(call_graph)
    #inlining_tree = build_inlining_tree(call_graph)
    #plot_inlining_tree(inlining_tree)



    #for fn in prog["functions"]:


    # print(states)
    #json.dump(prog, sys.stdout, indent=2)