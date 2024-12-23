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

def evaluate_inlining_tree(tree, prog, recursion_depth=1):
    result_map = defaultdict(int)
    def evaluate(tree):
        if isinstance(tree, InliningTreeLeaf):
            cleaned = tuple(clean_inlining_order(tree.inlined_edges))
            if cleaned not in result_map:
                result_map[cleaned] = implement_compile_measure(cleaned, prog, recursion_depth)
        elif isinstance(tree, InliningTreeBinaryNode):
            if tree.left:
                evaluate(tree.left)
            if tree.right:
                evaluate(tree.right)
        elif isinstance(tree, InliningTreeComponentsNode):
            for component in tree.components:
                evaluate(component)
    evaluate(tree)
    return result_map

def implement_inlining(inlined_edges, prog, recursion_depth):
    fns = dict((fn["name"], dict(fn)) for fn in prog["functions"])

    for caller_name, callee_name in inlined_edges:
        repeat = recursion_depth if caller_name == callee_name else 1
        for _ in range(repeat):
            new_instrs = []
            for caller_line in fns[caller_name]["instrs"]:
                if (caller_line.get("op") == "call") and (callee_name == caller_line["funcs"][0]):
                    # inline this function
                    chars = string.ascii_lowercase + string.ascii_uppercase
                    random_string = ''.join(random.choices(chars, k=10))
    
                    retval_name = caller_line.get("dest", None)
    
                    end_label = f"inline_terminate_{random_string}" # jump point to return to after inlined fn returns
    
                    # replace function arguments
                    if "args" in caller_line:
                        for arg, param in zip(caller_line["args"], fns[callee_name]["args"]):
                            pname  = param["name"] # param has name and type fields
                            new_instrs.append({"op": "id", "type": param["type"], "dest": f"{pname}_{random_string}", "args": [arg]})
                    # rename labels and var defs at the beginning
                    for cl in fns[callee_name]["instrs"]:
                        new_inst = dict(cl)
                        if "label" in cl: # rename label
                            curr_label = f"{cl['label']}_{random_string}"
                            new_inst["label"] = curr_label
                        if "dest" in cl: # var defn
                            curr_dest = f"{cl['dest']}_{random_string}"
                            new_inst["dest"] = curr_dest
                        if "args" in cl:
                            new_inst["args"] = list(cl["args"])
                            for i, arg in enumerate(cl["args"]):
                                curr_arg = f"{arg}_{random_string}"
                                new_inst["args"][i] = curr_arg
                        if "labels" in cl:
                            new_inst["labels"] = list(cl["labels"])
                            for i, label in enumerate(cl["labels"]):
                                curr_label = f"{label}_{random_string}"
                                new_inst["labels"][i] = curr_label
                        if "op" in cl and cl["op"] == "ret":
                            if retval_name is not None: 
                                new_instrs.append({"op": "id", "type": caller_line["type"], "dest": retval_name, "args": [f"{cl['args'][0]}_{random_string}"]})
                            new_inst = {}
                            new_inst["op"] = "jmp"
                            new_inst["labels"] = [end_label]
                        new_instrs.append(new_inst)
                    new_instrs.append({"label": end_label})
                else:
                    # no inlining on this instr
                    new_instrs.append(caller_line)
            # replace the old instrs with the new instrs
            fns[caller_name]["instrs"] = new_instrs
    new_prog = {"functions": list(fns.values())}
    return new_prog

def get_text_segment_size(executable_path):
    try:
        result = subprocess.run(['size', executable_path], 
                                stdout=subprocess.PIPE, 
                                stderr=subprocess.PIPE, 
                                text=True, 
                                check=True)
        
        output_lines = result.stdout.splitlines()
        if len(output_lines) < 2:
            raise ValueError("Unexpected output from size command.")
        
        header, data = output_lines[0], output_lines[1]
        size_values = data.split()
        if len(size_values) < 1:
            raise ValueError("Invalid size command output.")
        
        text_size = int(size_values[0])
        
        return text_size
    
    except subprocess.CalledProcessError as e:
        print(f"Error executing size command: {e.stderr.strip()}")
        return None
    except Exception as e:
        print(f"Error: {e}")
        return None

def implement_compile_measure(inlined_edges, prog, recursion_depth):
    implemented_prog = implement_inlining(inlined_edges, prog, recursion_depth)

    chars = string.ascii_lowercase + string.ascii_uppercase
    num = ''.join(random.choices(chars, k=10))
    
    temp_json_file = f"temp-bril-{num}.json"
    with open(temp_json_file, "w") as f:
        json.dump(implemented_prog, f, indent=2)

    try:
        brilift_output = f"bril-{num}.o"
        subprocess.run(f"brilift -o {brilift_output} -O speed_and_size < {temp_json_file}", shell=True, check=True)

        rt_location = "../../bril/brilift/rt.o"

        executable = f"myprog-{num}"
        subprocess.run(["cc", brilift_output, rt_location, "-o", executable], check=True)

        binary_size = get_text_segment_size(executable)

        return binary_size
    finally:
        if os.path.exists(temp_json_file):
            os.remove(temp_json_file)
        if os.path.exists(brilift_output):
            os.remove(brilift_output)
        if os.path.exists(executable):
            os.remove(executable)



if __name__ == "__main__":
    if len(sys.argv) > 1:
        depth = int(sys.argv[1])
    else:
        depth = 0

    prog = json.load(sys.stdin)
    # bin_size = implement_compile_measure([], prog)
    # print(bin_size)
    call_graph = get_call_graph(prog, depth == 0)
    plot_call_graph(call_graph)
    inlining_tree = build_inlining_tree(call_graph)
    #plot_inlining_tree(inlining_tree)
    result_map  = evaluate_inlining_tree(inlining_tree, prog, depth)
    print((), result_map[()])
    # print key of min value
    min_key = min(result_map, key=result_map.get)
    print(min_key, result_map[min_key])
    print(result_map)
    #for fn in prog["functions"]:


    # print(states)
    #json.dump(prog, sys.stdout, indent=2)