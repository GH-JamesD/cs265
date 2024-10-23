import json
import sys
import random
import string
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
    
def predss_and_successors(block_labels, blockmap):
    preds = defaultdict(set)
    succs = defaultdict(set)

    for i, name in enumerate(block_labels):
        block = blockmap[name]
        last_instr = block[-1]
        if 'op' in last_instr and last_instr['op'] == 'br':
            if 'labels' in last_instr:
                succs[name] = set(last_instr['labels'])
        elif 'op' in last_instr and last_instr['op'] == 'jmp':
            if 'labels' in last_instr:
                succs[name] = set([last_instr['labels'][0]])
        else:
            if i + 1 < len(blockmap):
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

        natural_loops.append(loop_nodes)
    return natural_loops

def is_pure_deterministic(instr):
    # extra conservative, some of these can be moved with careful analysis
    if instr["op"] in ["jmp", "br", "ret", "phi", "print", "call", "store", "load"]:
        return False
    if instr["op"] == "div":
        return False
    return True

def move_invariant_code(natural_loops, block_labels, blockmap, preds):
    pre_header_count = 1

    for loop in natural_loops:
        lines_to_move = {block: set() for block in loop} # need to preserve line order
        invariant_vars = set()

        defs_in_loop = set()
        for block in loop:
            for instr in blockmap[block]:
                if "dest" in instr:
                    defs_in_loop.add(instr["dest"])

        changed = True
        while changed: # not converged
            changed = False
            for block in loop:
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

            loop_header = max(loop, key=lambda b: len(dominators[b]))
            moved_instrs = []
            for block in loop: # TODO: do we need to iterate through blocks in a specific order?
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

            block_labels.insert(block_labels.index(loop_header), pre_header_label)
            blockmap[pre_header_label] = [{"label": pre_header_label}] + moved_instrs

            # redirect non-loop blocks to enter loop through pre-header
            for block in filter(lambda b: b not in loop, preds[loop_header]):
                jump_instr = blockmap[block][-1]
                for i, label in enumerate(jump_instr.get("labels", [])):
                    if label == loop_header:
                        jump_instr["labels"][i] = pre_header_label


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
        # blocks = list(blockmap.values())

        # print(find_natural_loops())
        natural_loops = find_natural_loops(block_labels, preds, succs, dominators)
        move_invariant_code(natural_loops, block_labels, blockmap, preds)

        #Up-to-date SSA instructions now in blockmap and blocks
        outinst = []
        for label in block_labels:
            block = blockmap[label]
            outinst.extend(block)
        fn["instrs"] = outinst


    json.dump(prog, sys.stdout, indent=2)