import json
import sys
import random
import string
from collections import defaultdict, OrderedDict, deque
from copy import deepcopy

from gvn import gvn

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
    cur_block = [{"label": "entry." + str(entryct)}]
    entryct += 1

    for instr in instrs:
        if 'op' in instr:  # It's an instruction.
            if not cur_block:
                cur_block.append({"label": "entry." + str(entryct)})
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
        # doms[name] = set(name for name in preds).union(set(name for name in succs))
        doms[name] = set(preds.keys())
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

def from_ssa(blockmap):
    for block in blockmap.values():
        for instr in reversed(block):
            if instr.get("op") == "phi":
                for label, arg in zip(instr.get("labels", []), instr.get("args", [])):
                    if arg == '__undefined':
                        continue
                    newdef = {"op": "id", "dest": instr["dest"], "args": [arg], "type": instr["type"]}
                    pred = blockmap[label]
                    if pred[-1].get("op") in TERMINATORS:
                        pred.insert(-1, newdef)
                    else:
                        pred.append(newdef)
                block.remove(instr)


var_nums = defaultdict(lambda: 1)

def fresh_name(var):
    global var_nums
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

        natural_loops.append((B, A, loop_nodes))
    return natural_loops

def redirect_control_flow(block, old_label, new_label):
    changed = False 
    for instr in block:
        if instr.get("op") in ["jmp", "br"]:
            if old_label in instr["labels"]:
                instr["labels"] = [new_label if l == old_label else l for l in instr["labels"]]
                changed = True
    return changed

def is_idempotent(instr):
    # extra conservative, some of these can be moved with careful analysis
    if instr["op"] in ["jmp", "br", "ret", "phi", "print", "call", "store", "load"]:
        return False
    return True

def normalize_loops(natural_loops, block_labels, blockmap, preds, succs, dominators):
    loop_cnt = 1

    normalized_loops = {}
    for header, body, loop_blocks in natural_loops:
        if header not in normalized_loops:
            preheader_label = "preheader." + str(loop_cnt)
            latch_label = "latch." + str(loop_cnt)
            loop_cnt += 1
            normalized_loops[header] = dict(
                body = [],
                preheader = preheader_label,
                latch = latch_label,
                # not strictly needed, but keeps the code nicer imo
                # just need to make sure latch not put after block without terminator
                last_pred = body, 
            )
            blockmap[preheader_label] = [{"label": preheader_label}]
            block_labels.insert(block_labels.index(header), preheader_label)
            for pred in preds[header]:
                if header not in dominators[pred]:
                    redirect_control_flow(blockmap[pred], header, preheader_label)

            blockmap[latch_label] = [{"label": latch_label}, {"op": "jmp", "labels": [header]}]
        # order doesn't matter as long as each path is in its original order
        normalized_loops[header]["body"].extend(loop_blocks - {header})
        redirect_control_flow(blockmap[body], header, normalized_loops[header]["latch"])
        normalized_loops[header]["last_pred"] = max(normalized_loops[header]["last_pred"], body, key=block_labels.index)
        
    for header, loop_info in normalized_loops.items():
        latch = loop_info["latch"]
        latch_succ = block_labels.index(loop_info["last_pred"]) + 1
        block_labels.insert(latch_succ, latch)

    return normalized_loops

def split_loops(normalized_loops, block_labels, blockmap, preds, succs):
    for header, loop_info in normalized_loops.items():
        loop_nodes = set([header] + loop_info["body"] + [loop_info["latch"]])
        preheader_label = loop_info["preheader"]
        # give up if it's too hard
        if len([succ for succ in succs[header] if succ in loop_nodes]) > 1:
            continue

        if any(succ not in loop_nodes for succ in succs[header]):
            loop_info["split"] = True

            header_copy = header + ".copy"
            blockmap[header_copy] = deepcopy(blockmap[header])
            blockmap[header_copy][0]["label"] = header_copy
            block_labels.insert(block_labels.index(preheader_label), header_copy)
            for pred in preds[header]:
                if pred not in loop_nodes:
                    redirect_control_flow(blockmap[pred], preheader_label, header_copy)
            for succ in succs[header]:
                if succ in loop_nodes:
                    # only one possible entry to loop body so it's fine
                    redirect_control_flow(blockmap[header_copy], succ, preheader_label)
                    blockmap[preheader_label].append({"op": "jmp", "labels": [succ]})
                

def move_invariant_code(normalized_loops, block_labels, blockmap, preds):
    for header, loop_info in normalized_loops.items():
        loop_blocks = set([header] + loop_info["body"] + [loop_info["latch"]])
        preheader_label = loop_info["preheader"]

        exits = set([succ for b in loop_blocks - {header} for succ in succs[b] if succ not in loop_blocks])
                     
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
                    # skip labels and already marked instructions
                    if ("op" not in instr) or (i in lines_to_move[block]):
                        continue
                    # mark LI if pure deterministic, dominates exits, and all fn args LI
                    if is_idempotent(instr) and all(
                        ((arg not in defs_in_loop) or (arg in invariant_vars))
                        for arg in instr.get("args", [])
                    ) and all(block in dominators[exit] for exit in exits):
                        lines_to_move[block].add(i)
                        if "dest" in instr:
                            invariant_vars.add(instr["dest"])
                        changed = True
        # fixed point reached, actually move LI code
        moved_instrs = []
        for block in loop_blocks: 
            kept_instrs_block = []
            for i, instr in enumerate(blockmap[block]):
                # update phi functions if var was moved
                if instr.get("op") == "phi":
                    for j, arg in enumerate(instr.get("args", [])):
                        if arg in invariant_vars:
                            instr["labels"][j] = preheader_label

                if i in lines_to_move[block]:
                    moved_instrs.append(instr)
                else:
                    kept_instrs_block.append(instr)
            blockmap[block] = kept_instrs_block
        if "split" in loop_info:
            jmp_instr = blockmap[preheader_label].pop()
            blockmap[preheader_label].extend(moved_instrs)
            blockmap[preheader_label].append(jmp_instr)
        else:
            blockmap[preheader_label].extend(moved_instrs)

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

def liveness_analysis(block_labels, blockmap, preds, succs, args):
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
    
        # Replace the function instructions with the optimized blocks

if __name__ == "__main__":
    prog = json.load(sys.stdin)
    for fn in prog["functions"]:
        block_labels = [b[0]["label"] for b in form_blocks(fn["instrs"])]
        blockmap = dict((b[0]["label"], b) for b in form_blocks(fn["instrs"]))
        preds, succs = predss_and_successors(block_labels, blockmap)
        dominators = compute_dominators(preds, succs)

        natural_loops = find_natural_loops(block_labels, preds, succs, dominators)
        normalized_loops = normalize_loops(natural_loops, block_labels, blockmap, preds, succs, dominators)
        split_loops(normalized_loops, block_labels, blockmap, preds, succs)

        # added new blocks, need to update preds and succs
        preds, succs = predss_and_successors(block_labels, blockmap)
        dominators = compute_dominators(preds, succs)
        fronts = compute_frontier(succs, dominators)
        tree = compute_tree(dominators)
        vardefs = find_vars(block_labels, blockmap)
        phis = place_phi(blockmap, fronts)
        rename_vars(fn["args"] if "args" in fn else [])

        move_invariant_code(normalized_loops, block_labels, blockmap, preds)
        gvn(block_labels[0], blockmap, succs, tree)

        from_ssa(blockmap)
        liveness_analysis(block_labels, blockmap, preds, succs, fn["args"] if "args" in fn else [])

        #Up-to-date SSA instructions now in blockmap and blocks
        outinst = []
        for label in block_labels:
            block = blockmap[label]
            outinst.extend(block)
        fn["instrs"] = outinst

    json.dump(prog, sys.stdout, indent=2)