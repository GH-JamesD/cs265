import json
import sys
import random
import string
import networkx as nx
from inlining_tree import *
from helpers import fresh_name
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
    fns = dict((fn["name"], fn) for fn in prog["functions"])
    G = nx.DiGraph()
    G.add_edges_from(inlined_edges)

    rev_topo = list(nx.topological_sort(G.reverse()))
    node_position = {node: i for i, node in enumerate(rev_topo)}
    inlined_edges = sorted(
    inlined_edges, key=lambda edge: (node_position[edge[0]], node_position[edge[1]]),
    )
    print(inlined_edges)
    for caller_name, callee_name in inlined_edges:
        new_instrs = []
        for caller_line in fns[caller_name]["instrs"]:
            if (caller_line.get("op") == "call") and (callee_name == caller_line["funcs"][0]):
                # inline this function
                retval_name = caller_line.get("dest", None)
                phi_labels = [] # for final phi instruction
                phi_vars = []   # for final phi instruction
                end_label = f"end_{fresh_name(callee_name)}" # jump point to return to after inlined fn returns
                old_to_new = {} # since code is in SSA form, a single map of old var names to new var names is enough
                old_to_new["__undefined"] = "__undefined"
                # replace function arguments
                for arg, param in zip(caller_line["args"], fns[callee_name]["args"]):
                    pname  = param["name"] # param has name and type fields
                    old_to_new[pname] = arg
                # rename labels and var defs at the beginning
                for cl in fns[callee_name]["instrs"]:
                    if "label" in cl: # rename label
                        curr_label = fresh_name(cl["label"])
                        old_to_new[cl["label"]] = curr_label
                    if "dest" in cl: # var defn
                        curr_dest = fresh_name(cl["dest"])
                        old_to_new[cl["dest"]] = curr_dest
                for callee_line in fns[callee_name]["instrs"]:
                    if "label" in callee_line:
                        curr_label = old_to_new[callee_line["label"]]
                        new_instrs.append({"label": curr_label})
                    elif callee_line["op"] == "ret":
                        # assumes well-formed fn: either all ret have a value or none do
                        if retval_name is not None:
                            # assumes no unlabeled blocks - our SSA fn guarantees this
                            phi_labels.append(curr_label)
                            phi_vars.append(old_to_new[callee_line["args"][0]])
                        new_instrs.append({"op": "jmp", "labels": [end_label]})
                    else:
                        new_line = dict(callee_line)
                        if "dest" in new_line:
                            new_line["dest"] = old_to_new[callee_line["dest"]]
                        # assumes no name collisions between vars and labels
                        if "args" in new_line:
                            new_line["args"] = [old_to_new[var] for var in new_line["args"]]
                        if "labels" in new_line:
                            new_line["labels"] = [old_to_new[var] for var in new_line["labels"]]
                        new_instrs.append(new_line)
                new_instrs.append({"label": end_label})
                if retval_name is not None:
                    new_instrs.append({"op": "phi", "dest": retval_name, "labels": phi_labels, "args": phi_vars})
            else:
                # no inlining on this instr
                new_instrs.append(caller_line)
        # replace the old instrs with the new instrs
        fns[caller_name]["instrs"] = new_instrs
    new_prog = {"functions": list(fns.values())}
    return new_prog


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
    # bin_size = implement_compile_measure([], prog)
    # print(bin_size)
    call_graph = get_call_graph(prog)
    plot_call_graph(call_graph)
    inlining_tree = build_inlining_tree(call_graph)
    #plot_inlining_tree(inlining_tree)
    evaluate_inlining_tree(inlining_tree, prog)

    #for fn in prog["functions"]:


    # print(states)
    #json.dump(prog, sys.stdout, indent=2)