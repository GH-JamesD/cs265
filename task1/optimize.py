import json
import sys
import random
import string

def generate_random_string(length=8):
    characters = string.ascii_letters
    random_string = ''.join(random.choice(characters) for i in range(length))
    return random_string

# Instructions that terminate a basic block.
TERMINATORS = 'br', 'jmp', 'ret'


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

##################### NEW CODE ############################

def is_pure(instr):
    side_effect = ("call", "print", "alloc", "free", "store", "load")
    return instr["op"] not in side_effect

def should_keep(instr, used):
    # not all instructions have an 'op' field, like labels
    if "op" not in instr:
        return True
    if "dest" not in instr:
        return instr["op"] != "nop"
    else:
        return instr["op"] != "nop" and not (is_pure(instr) and instr["dest"] not in used)

def lvn(block):
    maxval = 0
    val2num = {}
    num2val = {}
    var2num = {}
    num2var = {}

    for inst in block:
        #print(inst)
        if not "op" in inst or not "dest" in inst:
            continue
        if not "args" in inst and "value" in inst:
            value = tuple([inst["op"]] + [inst["value"]])
            num = maxval + 1
            maxval = num
            val2num[value] = num
            num2val[num] = value
        else:
            for arg in inst["args"]:
                if arg not in var2num:
                    num = maxval + 1
                    maxval = num
                    var2num[arg] = num
                    num2var[num] = arg

            args = [var2num[arg] for arg in inst["args"]]
            inst["args"] = [num2var[arg] for arg in args]
            value = tuple([inst["op"]] + args)

            num = val2num.get(value)

            if num is None: 
                num = maxval + 1
                maxval = num
                val2num[value] = num
                num2val[num] = value
            else:
                inst["op"] = "id"
                inst["args"] = [num2var[num]]

        if inst["dest"] in var2num:
            oldnum = var2num[inst["dest"]]
            tmpvar = generate_random_string()
            num2var[oldnum] = tmpvar
            var2num[tmpvar] = oldnum

            var2num[inst["dest"]] = num
            num2var[num] = inst["dest"]
        else:
            var2num[inst["dest"]] = num
            num2var[num] = inst["dest"]

    return block

def replace_or_dont(arg, replace):
    if arg in replace:
        return replace[arg]
    return arg

def local_dce(instrs):
    blocks = list(form_blocks(instrs))
    usedvars = {}
    def process_block(block):
        to_remove = []
        unused = {}
        replace = {}
        toblock = lvn(block) if len(list(blocks)) == 1 else block
        for inst in lvn(block):
            if "op" in inst and "id" in inst["op"]:
                replace[inst["dest"]] = replace_or_dont(inst["args"][0], replace)
                if inst["dest"] not in usedvars:
                    to_remove.append(inst)
                continue
            if "args" in inst:
                inst["args"] = [replace_or_dont(arg, replace) for arg in inst["args"]]
                for arg in inst["args"]:
                    unused.pop(arg, None)
            if "dest" in inst:
                if inst["dest"] in unused:
                    to_remove.append(unused[inst["dest"]])
                unused[inst["dest"]] = inst
        return [inst for inst in block if inst not in to_remove]


    out = []
    for block in reversed(blocks):
        insts = process_block(block)
        for inst in reversed(insts):
            out.append(inst)
            if "dest" in inst:
                usedvars.pop(inst["dest"], None)
            if "args" in inst:
                for arg in inst["args"]:
                    usedvars[arg] = 1
    return out[::-1]





if __name__ == "__main__":
    prog = json.load(sys.stdin)
    for fn in prog["functions"]:
        size = len(fn["instrs"])

        while True:
            fn["instrs"] = local_dce(fn["instrs"])
            used = []
            for instr in fn["instrs"]:
                if "args" in instr:
                    used.extend(instr["args"])
            fn["instrs"] = [instr for instr in fn["instrs"] if should_keep(instr, used)]
            if (len(fn["instrs"]) == size):
                break
            seenvars = []
            keepers = []
            for instr in reversed(fn["instrs"]):
                if "dest" not in instr or instr["dest"] in seenvars:
                    keepers.append(instr)
                if "args" in instr:
                    seenvars.extend(instr["args"])
            fn["instrs"] = keepers[::-1]
            size = len(fn["instrs"])
    json.dump(prog, sys.stdout, indent=2)