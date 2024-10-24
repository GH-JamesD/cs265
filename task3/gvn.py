from collections import defaultdict

cnt = 0
def gvn(label, blockmap, succs, dom_tree, val2num={}, num2val={}, var2num={}, num2var={}):
    val2num, num2val, var2num, num2var = val2num.copy(), num2val.copy(), var2num.copy(), num2var.copy()
    block = blockmap[label]
    global cnt

    # for phi node, remove and continue if meaningless or redundant
    for inst in block:
        if inst.get("op") == "phi":
            if len(set(inst.get("args", [])) - {inst["dest"]}) == 0:
                block.remove(inst)

    for inst in block:
        if "value" in inst:
            value = tuple([inst["op"]] + [inst["value"]])
            if value not in val2num:
                cnt += 1
                num = cnt
                val2num[value] = num
                num2val[num] = value
        elif "args" in inst:
            for arg in inst["args"]:
                if arg not in var2num:
                    cnt += 1
                    num = cnt
                    var2num[arg] = num
                    num2var[num] = arg

            args = [var2num[arg] for arg in inst["args"]]
            inst["args"] = [num2var[arg] for arg in args]
            value = tuple([inst["op"]] + args)

            if inst["op"] == "id":
                num = var2num[inst["args"][0]]
            else:
                num = val2num.get(value)

            if num is not None: 
                inst["op"] = "id"
                inst["args"] = [num2var[num]]
            else:
                cnt += 1
                num = cnt
                val2num[value] = num
                # num2val[num] = value

            if "dest" in inst:
                var2num[inst["dest"]] = num
                num2var[num] = inst["dest"]
    
    for child in succs[label]:
        # replace all phi node operands in c that were computed in this block with their value numbers
        for inst in blockmap[child]:
            if inst.get("op") == "phi":
                inst["args"] = [num2var.get(var2num.get(arg), arg) for arg in inst.get("args", [])]


    for child in dom_tree[label]:
        gvn(child, blockmap, succs, dom_tree, val2num, num2val, var2num, num2var)