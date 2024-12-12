import json
import sys
import numpy as np
import pandas as pd
import subprocess


if __name__ == "__main__":
    prog = json.load(sys.stdin)
    loc_count = 0
    for fn in prog["functions"]:
        for instr in fn["instrs"]:
            if "op" in instr:
                loc_count += 1

    print(loc_count)

