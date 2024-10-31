import json
import sys
import random
import string
from utils import *
from collections import defaultdict, OrderedDict, deque

TERMINATORS = 'br', 'jmp', 'ret'

# blocks = []
# blockmap = {}
# preds = set()
# succs = set()
# dominators = {}
# fronts  = {}
# tree = {}
# vardefs = {}
# phis = {}

def form_blocks(instrs):
    """Given a list of Bril instructions, generate a sequence of
    instruction lists representing the basic blocks in the program.

    Every instruction in `instr` will show up in exactly one block. Jump
    and branch instructions may only appear at the end of a block, and
    control can transfer only to the top of a basic block---so labels
    can only appear at the *start* of a basic block. Basic blocks may
    not be empty.
    """
    entryct = 1

    # Start with an entry label to deal with ill-formed CFGs.
    cur_block = [{"label": "entry" + str(entryct)}]
    entryct += 1

    for instr in instrs:
        if 'op' in instr:  # It's an instruction.
            if not cur_block:
                cur_block.append({"label": "entry" + str(entryct)})
                entryct += 1
            # Add the instruction to the currently-being-formed block.
            cur_block.append(instr)

            # If this is a terminator (branching instruction), it's the
            # last instruction in the block. Finish this block and
            # start a new one.
            if instr['op'] in TERMINATORS:
                yield cur_block
                cur_block = []

        else:  # It's a label.
            # End the block here (if it contains anything).
            if cur_block:
                yield cur_block

            # Start a new block with the label.
            cur_block = [instr]

    # Produce the final block, if any.
    if cur_block:
        yield cur_block
    
def predss_and_successors(block_labels, blockmap):
    preds = defaultdict(set)
    succs = defaultdict(set)

    for i, name in enumerate(block_labels):
        block = blockmap[name]
        last_instr = block[-1]
        if last_instr.get('op') == 'br':
            if 'labels' in last_instr:
                succs[name] = set(last_instr['labels'])
        elif last_instr.get('op') == 'jmp':
            if 'labels' in last_instr:
                succs[name] = set([last_instr['labels'][0]])
        elif last_instr.get('op') == 'ret':
            succs[name] = set()
        else:
            if i + 1 < len(block_labels):
                succs[name] = set([block_labels[i + 1]])
        for s in succs[name]:
            preds[s].add(name)

    return preds, succs

def reverse_postorder(succs):
    visited = set()
    postorder = []

    def dfs(node):
        visited.add(node)
        for s in succs.get(node, []):
            if s not in visited:
                dfs(s)
        postorder.append(node)

    for node in succs:
        if node not in visited:
            dfs(node)

    return postorder[::-1]

def compute_dominators(preds, succs):
    doms = defaultdict(set)
    for name in preds.keys():
        doms[name] = set(name for name in preds).union(set(name for name in succs))
        #doms[name] = set(preds.keys())
    changed = True
    rev_post = reverse_postorder(succs)
    while changed:
        changed = False
        for i in rev_post:
            new = {i}
            if (preds[i]):
                new = new.union(set.intersection(*[doms[j] for j in preds[i]]))
            
            if new != doms[i]:
                doms[i] = new
                changed = True
    return doms

def is_idom(p, b):
    return all([p not in dominators[node] for node in dominators[b] - {b} - {p}]) and p in (dominators[b] - {b})

def get_idoms():
    idoms = defaultdict(str)
    for b in preds.keys() | succs.keys():
        for p in dominators[b]:
            if is_idom(p, b):
                idoms[b] = p
    return idoms


def compute_frontier(succs, dominators):
    rev_dominators = defaultdict(set)
    for dom in dominators:
        for domd in dominators[dom]:
            rev_dominators[domd].add(dom)

    frontier = defaultdict(set)
    for dom in dominators:
        domset = set()
        for domd in rev_dominators[dom]:
                domset = domset | succs[domd]
        for item in domset:
            if item not in rev_dominators[dom] or item == dom:
                frontier[dom].add(item)
    return frontier


def compute_tree(dominators):
    rev_dominators = defaultdict(set)
    for dom in dominators:
        for domd in dominators[dom]:
            rev_dominators[domd].add(dom)

    two_away = defaultdict(set)

    for dom in rev_dominators:
        for item in rev_dominators[dom] - {dom}:
            two_away[dom] = two_away[dom] | (rev_dominators[item] - {item})

    dom_tree = defaultdict(set)

    for dom in rev_dominators:
        for item in rev_dominators[dom] - {dom}:
            if item not in two_away[dom]:
                dom_tree[dom] = dom_tree[dom] | {item}
    
    return dom_tree

def find_vars(block_labels, blockmap):
    vardefs = defaultdict(set)
    for label in block_labels:
        block = blockmap[label]
        for instr in block:
            if "dest" in instr:
                vardefs[instr["dest"]].add(block[0]["label"])
    return vardefs

def place_phi(blockmap, fronts):
    global vardefs
    phis = defaultdict(list)
    for var in vardefs.keys():
        blocks_to_add_phi = defaultdict(set)
        for def_block in vardefs[var]:
            for block in fronts[def_block]:
                blocks_to_add_phi[block].add(def_block)
        for block in blocks_to_add_phi:
            vartype = ""
            for inst in blockmap[next(iter(blocks_to_add_phi[block]))]:
                if "dest" in inst and inst["dest"] == var:
                    vartype = inst["type"]
            newinst = {"op": "phi", "dest": var, "og": var, "type": vartype, "args": [], "labels": []}
            vardefs[var].add(block)
            phis[block].append(newinst)
    return phis

def remove_dots(inst):
    if "dest" in inst:
        newdest = inst["dest"].split(".")
        if len(newdest) > 0:
            inst["dest"] = newdest[0]
    if "args" in inst:
        newargs = []
        for arg in inst["args"]:
            newarg = arg.split(".")
            if len(newarg) > 0:
                newargs.append(newarg[0])
        inst["args"] = newargs

def from_ssa(blockmap):
    for block in blockmap.values():
        for instr in reversed(block):
            if instr.get("op") == "phi":
                for label, arg in zip(instr.get("labels", []), instr.get("args", [])):
                    if arg == '__undefined':
                        continue
                    newdef = {"op": "id", "dest": instr["dest"], "args": [arg], "type": instr["type"]}
                    remove_dots(newdef)
                    pred = blockmap[label]
                    if pred[-1].get("op") in TERMINATORS:
                        pred.insert(-1, newdef)
                    else:
                        pred.append(newdef)
                block.remove(instr)
            else:
                remove_dots(instr)


var_nums = defaultdict(lambda: 1)

def fresh_name(var):
    global var_nums
    out = var  + "." + str(var_nums[var])
    var_nums[var] += 1
    return out

def rename_vars(args):
    stack = defaultdict(list, {arg["name"]: [arg["name"]] for arg in args})

    def rename_block(block):
        nonlocal stack
        oldstack = {var: list(stack) for var, stack in stack.items()}
        for phi in phis[block]:
            fresh = fresh_name(phi["dest"])
            stack[phi["dest"]].append(fresh)
            phi["dest"] = fresh
        for inst in blockmap[block]:
            if "op" in inst:
                if "args" in inst:
                    inst["args"] = [stack[arg][-1] for arg in inst["args"]]
                if "dest" in inst:
                    fresh = fresh_name(inst["dest"])
                    stack[inst["dest"]].append(fresh)
                    inst["dest"] = fresh
        for succ in succs[block]:
            for phi in phis[succ]:
                v = phi["og"]
                if stack[v]:
                    phi["args"].append(stack[v][-1])
                    phi["labels"].append(block)
                else:
                    phi["args"].append("__undefined")
                    phi["labels"].append(block)
        for child in tree[block]:
            rename_block(child)
        
        stack.clear()
        stack.update(oldstack)

    first = list(succs.keys())[0]
    rename_block(first)

    for block, phies in phis.items():
        for phi in phies:
            if (phi["args"]):
                phi.pop("og")
                if len(blockmap[block]) > 1:
                    blockmap[block] = [blockmap[block][0]] + [phi] + blockmap[block][1:]
                else:
                    blockmap[block] = [blockmap[block][0]] + [phi]

def find_natural_loops(block_labels, preds, succs, dominators):
    backedges = []
    for label in block_labels:
        name1 = label
        for name2 in succs[name1]:
            if name2 in dominators[name1]:
                backedges.append((name1, name2))

    natural_loops = []
    for (A, B) in backedges:
        loop_nodes = set((A, B))
        worklist = deque([A])
        while worklist:
            node = worklist.popleft()
            for pred in preds[node]:
                if pred not in loop_nodes:
                    loop_nodes.add(pred)
                    worklist.append(pred)

        natural_loops.append((B, loop_nodes))
    return natural_loops

def is_pure_deterministic(instr):
    # extra conservative, some of these can be moved with careful analysis
    if instr["op"] in ["jmp", "br", "ret", "phi", "print", "call", "store", "load"]:
        return False
    if instr["op"] == "div":
        return False
    return True

def move_invariant_code(natural_loops, block_labels, blockmap, preds, dominators):
    pre_header_count = 1

    for header, loop_blocks in natural_loops:
        lines_to_move = {block: set() for block in loop_blocks} # need to preserve line order
        invariant_vars = set()

        defs_in_loop = set()
        for block in loop_blocks:
            for instr in blockmap[block]:
                if "dest" in instr:
                    defs_in_loop.add(instr["dest"])

        changed = True
        while changed: # not converged
            changed = False
            for block in loop_blocks:
                for i, instr in enumerate(blockmap[block]):
                    # skip labels
                    if "op" not in instr:
                        continue
                    if i in lines_to_move[block]:
                        continue
                    # mark LI if pure deterministic and all fn args LI
                    if is_pure_deterministic(instr) and all(
                        (arg not in defs_in_loop) or (arg in invariant_vars)
                        for arg in instr.get("args", [])
                    ):
                        lines_to_move[block].add(i)
                        if "dest" in instr:
                            invariant_vars.add(instr["dest"])
                        changed = True
    
        # create pre-header to hold moved instructions
        if any(ll for ll in lines_to_move.values()):
            pre_header_label = "preheader" + str(pre_header_count)
            pre_header_count += 1

            moved_instrs = []
            for block in loop_blocks: # TODO: do we need to iterate through blocks in a specific order?
                kept_instrs_block = []
                for i, instr in enumerate(blockmap[block]):
                    # update phi functions if var was moved
                    if instr.get("op") == "phi":
                        for j, arg in enumerate(instr["args"]):
                            if arg in invariant_vars:
                                instr["labels"][j] = pre_header_label

                    if i in lines_to_move[block]:
                        moved_instrs.append(instr)
                    else:
                        kept_instrs_block.append(instr)
                blockmap[block] = kept_instrs_block

            block_labels.insert(block_labels.index(header), pre_header_label)
            blockmap[pre_header_label] = [{"label": pre_header_label}] + moved_instrs

            # redirect non-loop blocks to enter loop through pre-header
            for block in filter(lambda b: b not in loop_blocks, preds[header]):
                jump_instr = blockmap[block][-1]
                for i, label in enumerate(jump_instr.get("labels", [])):
                    if label == header:
                        jump_instr["labels"][i] = pre_header_label





def liveness_analysis(block_labels, blockmap, preds, succs, args):
    def meet(in_sets):
        if not in_sets:
            return set()
        result = set(in_sets[0])
        for in_set in in_sets[1:]:
            result.update(in_set)
        return result

    def transfer(block, out_set):
        kills = set()
        gens = set()

        for instr in reversed(block):
            if "dest" in instr:
                kills.add(instr["dest"])
            gens.update(arg for arg in instr.get("args", []))

        out = gens | (set(out_set) - kills)
        return block, out

    blocks = blockmap
    # Initialize in/out sets for each block
    in_sets = {label: set() for label in block_labels}
    out_sets = {label: set() for label in block_labels}
    worklist = deque(block_labels)
    for arg in args:
        in_sets[block_labels[0]].add(arg["name"])

    while worklist:
        b = worklist.pop()
        # Compute out[b] as the meet of in[successors]
        out_sets[b] = meet([in_sets[succ] for succ in succs[b]])
        # Propagate constants within the block
        new_block, in_set = transfer(blocks[b], out_sets[b])
        if in_sets[b] != in_set:
            in_sets[b] = in_set
            worklist.extend(preds[b])
        blocks[b] = new_block

    for i in block_labels:
        kept = []
        used = set()
        for instr in reversed(blocks[i]):
            if "dest" not in instr:
                kept.append(instr)
            if "dest" in instr and (instr["dest"] in out_sets[i] or instr["dest"] in used):
                kept.append(instr)
            used.update(instr.get("args", []))
        blocks[i] = kept[::-1]
    


def evaluate_expression(instr, constants):
    try:
        if instr["op"] == "add":
            return constants[instr["args"][0]] + constants[instr["args"][1]]
        elif instr["op"] == "sub":
            return constants[instr["args"][0]] - constants[instr["args"][1]]
        elif instr["op"] == "mul":
            return constants[instr["args"][0]] * constants[instr["args"][1]]
        elif instr["op"] == "div" and constants[instr["args"][1]] != 0:
            return constants[instr["args"][0]] // constants[instr["args"][1]]
        elif instr["op"] == "const":
            return instr["value"]
    except KeyError:
        pass
    return None

def propagate_constants_in_block(block, in_constants):
    out_constants = in_constants.copy()
    new_instrs = []

    for instr in block:
        if instr.get("op") == "const":
            out_constants[instr["dest"]] = instr["value"]
            new_instrs.append(instr)
        elif "args" in instr:
            if all(arg in out_constants for arg in instr["args"]):
                result = evaluate_expression(instr, out_constants)
                if result is not None:
                    new_instrs.append({"op": "const", "dest": instr["dest"], "type": instr["type"], "value": result})
                    out_constants[instr["dest"]] = result
                else:
                    new_instrs.append(instr)
            else:
                new_instrs.append(instr)
        else:
            new_instrs.append(instr)

        if instr.get("op") == "mov" and instr["args"][0] in out_constants:
            out_constants[instr["dest"]] = out_constants[instr["args"][0]]

    return new_instrs, out_constants

def constant_propagation_and_folding(block_labels, blockmap, preds, succs):
    def meet(in_sets):
        """Perform the meet operation for constants (intersection of known constants)."""
        if not in_sets:
            return {}
        result = in_sets[0].copy()
        for in_set in in_sets[1:]:
            for var in list(result):
                if var not in in_set or result[var] != in_set[var]:
                    del result[var]
        return result

    blocks = blockmap

    # Initialize in/out sets for each block
    in_sets = {label: defaultdict(lambda: None) for label in block_labels}
    out_sets = {label: defaultdict(lambda: None) for label in block_labels}
    worklist = deque(reversed(block_labels))
    while worklist:
        b = worklist.pop()
        # Compute in[b] as the meet of out[predecessors]
        if preds[b]:
            in_sets[b] = meet([out_sets[p] for p in preds[b]])
        # Propagate constants within the block
        new_block, out_constants = propagate_constants_in_block(blocks[b], in_sets[b])
        if out_sets[b] != out_constants:
            out_sets[b] = out_constants
            worklist.extend(succs[b])
        blocks[b] = new_block


def lvn(block, val2num = None, num2val = None, var2num = None, num2var = None):
    if val2num is None:
        val2num = {}
    if num2val is None:
        num2val = {}
    if var2num is None:
        var2num = {}
    if num2var is None:
        num2var = {}
    counter = len(val2num) # TODO: different dominator tree children could have overlapping value numbers, is that ok?
    # counter = 0

    for inst in block:
        if "dest" not in inst:
            continue
        if not isinstance(inst["type"], str):
            continue

        # if inst["op"] not in ["add", "mul", "sub", "div", "eq", "lt", "gt", "le", "ge", "not", "and", "or", "id", "phi"]:
        if inst["op"] not in ["add", "mul", "sub", "div", "eq", "lt", "gt", "le", "ge", "not", "and", "or", "id"]:
            counter += 1
            num = counter
            num2val[num] = None
        else:
            args = []
            if "args" in inst:
                for idx, arg in enumerate(inst["args"]):
                    argnum = var2num.get(arg)
                    if argnum is None:
                        args.append(arg)
                    else:
                        if num2var[argnum][0] != arg:
                            inst["args"][idx] = num2var[argnum][0]
                        args.append("#." + str(argnum))
            if inst["op"] in ["add", "mul"]:
                args.sort()
            if inst["op"] == "const":
                valstring = "const " + str(inst['value'])
            elif inst["op"] == "phi":
                args_sorted, labels_sorted = zip(*filter(lambda pair: pair[0] != "__undefined", sorted(zip(inst["labels"], inst["args"]))))
                valstring = str(inst['op']) + str(inst['type']) + str(args_sorted) + str(labels_sorted)
            else:
                valstring = str(inst['op']) + str(inst['type']) + str(args)

            if inst["op"] == "id":
                num = var2num.get(inst["args"][0])
            else:
                num = val2num.get(valstring)

            if num is None:
                counter += 1
                num = counter
                val2num[valstring] = num
                num2val[num] = valstring
            else:
                inst["op"] = "id"
                inst["args"] = [num2var[num][0]]
                inst.pop("funcs", None)

        if inst["dest"] in var2num:
            oldnum = var2num[inst["dest"]]
            num2var[oldnum].remove(inst["dest"])
            if len(num2var[oldnum]) == 0:
                old_value = num2val.get(oldnum)
                if old_value is not None:
                    val2num.pop(old_value)
                num2val.pop(oldnum)

        var2num[inst["dest"]] = num
        if num not in num2var:
            num2var[num] = [inst["dest"]]
        else:
            num2var[num].append(inst["dest"])

    return block

def gvn(func, blocks, blockmap, dominators, tree, succs):
    val2num = {}
    num2val = {}
    var2num = {}
    num2var = {}
    counter = 0

    # number function args
    for arg in func.get("args", []):
        counter += 1
        num = counter
        val2num[arg["name"]] = num
        num2val[num] = arg["name"] # TODO: I think this is fine?
        var2num[arg["name"]] = num
        num2var[num] = [arg["name"]]

    entry_block = min(blocks, key=lambda b: len(dominators[b]))

    gvn_helper(entry_block, blockmap, tree, succs, val2num, num2val, var2num, num2var)

def gvn_helper(block, blockmap, tree, succs, val2num: dict, num2val: dict, var2num: dict, num2var:dict):
    # remove trivial phis
    for inst in blockmap[block]:
        if inst.get("op") == "phi":
            args_sorted, labels_sorted = zip(*filter(lambda pair: pair[1] != "__undefined", sorted(zip(inst["labels"], inst["args"]))))
            # useless or trivial phi
            if len(set(var2num.get(arg, arg) for arg in args_sorted)) == 1:
                inst["op"] = "id"
                inst["args"] = [args_sorted[0]]
                inst.pop("labels", None)
                continue
            # no need to handle phi functions now, LVN pass will do it for us
    lvn(block, val2num, num2val, var2num, num2var)

    for child in tree[block]:
        gvn_helper(child, blockmap, tree, succs, val2num.copy(), num2val.copy(), var2num.copy(), num2var.copy())
def returns_ptr(instr):
    # account for both type="ptr" and type={"ptr", <Type>}
    return "ptr" in instr.get("type", "")

def alias_analysis(block_labels, blockmap, preds, arg_state=AliasLattice()):
    constants = {inst["dest"]: inst["value"] for block in blockmap.values() for inst in block if inst.get("op") == "const"}

    heap_cnt = 1
    all_heap = AliasLattice("ALL_HEAP")

    def meet(states):
        out_states = {}
        print('states', set(tuple(s.keys()) for s in states))
        for v in set(tuple(s.keys()) for s in states):
            out_states[v] = AliasLattice.union(*[s.get(v, AliasLattice()) for s in states])
        return out_states

    def transfer(block, in_state):
        nonlocal heap_cnt

        out_state = in_state.copy()
        for instr in block:
            if returns_ptr(instr):
                name = instr.get("dest")
                if instr.get("op") == "alloc":
                    mem_region = HeapLoc(heap_cnt)
                    out_state[name] = AliasLattice([mem_region])
                    heap_cnt += 1
                elif instr.get("op") == "id":
                    rhs = instr["args"][0]
                    out_state[name] = out_state.get(rhs, all_heap)
                elif instr.get("op") == "ptradd":
                    # assumes some level of constant prop/folding
                    ptr, offset = instr["args"]
                    if out_state.get(ptr, all_heap) == all_heap:
                        out_state[name] = all_heap
                    else:
                        for memloc in out_state[name]:
                            memloc.update_offset(constants.get(offset, ANY_OFFSET))
                elif instr.get("op") == "load":
                    # could be loading another pointer, assume
                    # could point to anything
                    out_state[instr["dest"]] = all_heap

        # bookkeeping to clean up big offset chains that we could have made
        return out_state
    
    # Initialize in/out sets for each block
    in_states = {label: arg_state for label in block_labels}
    out_states = {label: arg_state for label in block_labels}

    # worklist = deque(block_labels[::-1]) 
    worklist = deque(block_labels) 
    # order doesn't matter, but theoretically topological order is best
    while worklist:
        b = worklist.pop()
        in_states[b] = meet([out_states[pred] for pred in preds[b]])
        # print(in_states[b], [out_states[pred] for pred in preds[b]])
        new_out = transfer(blockmap[b], in_states[b])
        if out_states[b] != new_out:
            out_states[b] = new_out
            worklist.extend(succs[b])

    return meet(out_states.values())

def local_dead_store_elim(block, aliases):
    unused_stores = {}
    for instr in block:
        if instr.get("op") == "load": 
            for ptr in unused_stores.keys():
                # may be loaded from 
                if aliases[instr["args"][0]].intersection(aliases[ptr]):
                    unused_stores.pop(ptr)
        if instr.get("op") == "store":
            if instr["args"][0] in unused_stores:
                block.remove(unused_stores[instr["args"][0]])
            unused_stores[instr["args"][0]] = instr

def may_alias(ptr1, ptr2, aliases):
    if must_alias(ptr1, ptr2, aliases):
        return True
    return aliases[ptr1].intersection(aliases[ptr2])

def must_alias(ptr1, ptr2, aliases):
    if ptr1 == ptr2:
        return True
    if aliases[ptr1] == ALL_HEAP or aliases[ptr2] == ALL_HEAP:
        return False
    if any(loc.endswith(".any") for loc in aliases[ptr1]) or any(loc.endswith(".any") for loc in aliases[ptr2]):
        return False
    return aliases[ptr1] == aliases[ptr2]

def local_store_to_load(block, state_must):
    most_recent_stores = {}
    for instr in block:
        if instr.get("op") == "store":
            most_recent_stores[instr["args"][0]] = instr
        if instr.get("op") == "load":
            for ptr in most_recent_stores.keys():
                if must_alias(ptr, instr["args"][0], state_must):
                    instr["op"] = "id"
                    instr["args"] = [most_recent_stores[ptr]["dest"]]

def local_redundant_load_elim(block, state):
    unused_loads = {}
    for instr in block:
        if instr.get("op") == "store":
            for ptr in unused_loads.keys():
                if may_alias(ptr, instr["args"][0], state):
                    unused_loads.pop(ptr)
        if instr.get("op") == "load":
            for ptr in unused_loads.keys():
                if must_alias(ptr, instr["args"][0], state):
                    instr["op"] = "id"
                    instr["args"] = [unused_loads[ptr]["dest"]]

def should_keep(instr, used_vars):
    if 'op' not in instr or 'dest' not in instr:
        return True
    return instr['dest'] in used_vars

if __name__ == "__main__":
    prog = json.load(sys.stdin)
    for fn in prog["functions"]:
        block_labels = [b[0]["label"] for b in form_blocks(fn["instrs"])]
        blockmap = dict((b[0]["label"], b) for b in form_blocks(fn["instrs"]))
        preds, succs = predss_and_successors(block_labels, blockmap)
        dominators = compute_dominators(preds, succs)
        fronts = compute_frontier(succs, dominators)
        tree = compute_tree(dominators)
        vardefs = find_vars(block_labels, blockmap)
        phis = place_phi(blockmap, fronts)
        rename_vars(fn["args"] if "args" in fn else [])
        usedvars = set()
        for label in block_labels:
            for inst in blockmap[label]:
                args = inst.get("args", [])
                usedvars.update(args)
        
        for label in block_labels:
            outmap = []
            for inst in blockmap[label]:
                if should_keep(inst, usedvars):
                    outmap.append(inst)
            blockmap[label] = outmap        
            
        natural_loops = find_natural_loops(block_labels, preds, succs, dominators)

        move_invariant_code(natural_loops, block_labels, blockmap, preds, dominators)

        preds, succs = predss_and_successors(block_labels, blockmap)
        dominators = compute_dominators(preds, succs, block_labels)
        fronts = compute_frontier(succs, dominators)
        tree = compute_tree(dominators)

        state = alias_analysis(block_labels, blockmap, preds)

        for label in block_labels:
            block = blockmap[label]
            local_dead_store_elim(block, state)
            local_store_to_load(block, state)
            local_redundant_load_elim(block, state)

        for label in block_labels:
            block = blockmap[label]
            blockmap[label] = lvn(block)
        # gvn(fn, block_labels, blockmap, dominators, tree, succs)

        from_ssa(blockmap)
        liveness_analysis(block_labels, blockmap, preds, succs, fn["args"] if "args" in fn else [])
        constant_propagation_and_folding(block_labels, blockmap, preds, succs)



        #Up-to-date SSA instructions now in blockmap and blocks
        outinst = []
        for label in block_labels:
            block = blockmap[label]
            for inst in block:
                if "op" in inst and inst["op"] == "id":
                    if inst["dest"] == inst["args"][0]:
                        continue
                outinst.append(inst)
        fn["instrs"] = outinst

    print("May alias")
    print(state_may)
    print("Must alias")
    print(state_must)
    # json.dump(prog, sys.stdout, indent=2)