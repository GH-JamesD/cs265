import json
import sys
import random
import string
from collections import defaultdict

TERMINATORS = 'br', 'jmp', 'ret'

blocks = []
preds = set()
succs = set()
dominators = {}
fronts  = {}

def form_blocks(instrs):
    """Given a list of Bril instructions, generate a sequence of
    instruction lists representing the basic blocks in the program.

    Every instruction in `instr` will show up in exactly one block. Jump
    and branch instructions may only appear at the end of a block, and
    control can transfer only to the top of a basic block---so labels
    can only appear at the *start* of a basic block. Basic blocks may
    not be empty.
    """

    # Start with an empty block.
    cur_block = []

    for instr in instrs:
        if 'op' in instr:  # It's an instruction.
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
    front = defaultdict(set)
    idoms = get_idoms()
    for b in preds.keys() | succs.keys():
        if len(preds[b]) >= 2:
            for p in preds[b]:
                runner = p
                while p != idoms[b]:
                    front[runner].add(b)
                    if (idoms[runner]):
                        runner = idoms[runner]
                    else:
                        break
    return front
    


if __name__ == "__main__":
    prog = json.load(sys.stdin)
    for fn in prog["functions"]:
        blocks = list(form_blocks(fn["instrs"]))
        preds, succs = predss_and_successors(blocks)
        dominators = compute_dominators()
        fronts = compute_frontier()
        print(fronts)

    #7json.dump(prog, sys.stdout, indent=2)