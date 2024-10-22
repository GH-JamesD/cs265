import json
import sys
import random
import string
from collections import defaultdict

TERMINATORS = 'br', 'jmp', 'ret'

blocks = []
blockmap = {}
preds = set()
succs = set()
dominators = {}
fronts  = {}
tree = {}
vardefs = {}
phis = {}

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

    # Start with an empty block.
    cur_block = []

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
    


def predss_and_successors(blocks):
    preds = defaultdict(set)
    succs = defaultdict(set)

    for i, block in enumerate(blocks):
        last_instr = block[-1]
        name = block[0]["label"]
        if 'op' in last_instr and last_instr['op'] == 'br':
            if 'labels' in last_instr:
                succs[name] = set(last_instr['labels'])
        elif 'op' in last_instr and last_instr['op'] == 'jmp':
            if 'labels' in last_instr:
                succs[name] = set([last_instr['labels'][0]])
        else:
            if i + 1 < len(blocks):
                succs[name] = set([blocks[i + 1][0]["label"]])
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

def compute_dominators():
    doms = defaultdict(set)
    for name in preds:
        doms[name] = set(name for name in preds).union(set(name for name in succs))
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


def compute_frontier():
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


def compute_tree():
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

def find_vars():
    vardefs = defaultdict(set)
    for block in blocks:
        for instr in block:
            if "dest" in instr:
                vardefs[instr["dest"]].add(block[0]["label"])
    return vardefs

def place_phi():
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


var_nums = defaultdict(int)

def fresh_name(var):
    global var_nums
    if var not in var_nums:
        var_nums[var] = 1
    out = var + str(var_nums[var])
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





if __name__ == "__main__":
    prog = json.load(sys.stdin)
    for fn in prog["functions"]:
        blocks = list(form_blocks(fn["instrs"]))
        blockmap = {b[0]["label"]: b for b in blocks}
        preds, succs = predss_and_successors(blocks)
        dominators = compute_dominators()
        fronts = compute_frontier()
        tree = compute_tree()
        vardefs = find_vars()
        phis = place_phi()
        rename_vars(fn["args"] if "args" in fn else [])
        blocks = list(blockmap.values())
        #Up-to-date SSA instructions now in blockmap and blocks
        outinst = []
        for block in blocks:
            outinst.extend(block)
        fn["instrs"] = outinst
    json.dump(prog, sys.stdout, indent=2)