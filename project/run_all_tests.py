import os
import subprocess
import numpy as np
from matplotlib import pyplot as plt
import pandas as pd
import subprocess
import tqdm

def find_bril_files(directory):
    """Find all files ending with .bril in the specified directory and its subdirectories."""
    bril_files = []
    for root, _, files in os.walk(directory):
        for file in files:
            if file.endswith(".bril"):
                # check if file contains the string 'call'
                with open(os.path.join(root, file), 'r') as f:
                    if 'call' in f.read():
                        bril_files.append(os.path.join(root, file))
    return bril_files


def run_command_on_files(bril_files, command_template):
    """Run the specified command on each .bril file."""
    results = []
    for bril_file in bril_files:
        result = 0
        print(bril_file)
        command = command_template.format(file=bril_file)
        try:
            print(f"Running command: {command}")
            result = str(subprocess.check_output(command, timeout=2))
        except Exception as e:
            print(f"Error while running command on {bril_file}, running for two seconds, stopping it now {e}")
        
        results.append(result)
    return results


if __name__ == "__main__":
    directory_to_search = "../../bril/benchmarks/core"

    bench_cmds = dict(
        #baseline = "cat {file} | bril2json | python ../../bril/examples/to_ssa.py | python ../../bril/examples/from_ssa.py",
        inlining = "cat {file} | bril2json | python ../../bril/examples/to_ssa.py | python inlining.py"
        # ssa = "cat {file} | bril2json | python optimize.py --no-licm",
        # licm = "cat {file} | bril2json | python optimize.py",
    )

    bril_files = find_bril_files(directory_to_search)

    res_dict = {}

    analyses = dict(
        #total_len = "python count_instrs.py",
        # loop_loc = "python count_loop_loc.py",
    )

    if bril_files:
        print(f"Found {len(bril_files)} .bril files.")
        out = dict(
            benchmark = [],
            run = [],
            results = []
        )
        for file in tqdm.tqdm(bril_files):
            for title, cmd in bench_cmds.items():
                out["benchmark"].append(file.split("/")[-1].split(".")[0])
                out["run"].append(title)
                out["results"].append(run_command_on_files([file], cmd)[0])

            
        df = pd.DataFrame(out, columns=out.keys())
        df.to_csv("tests.csv", index=False)
    else:
        print("No .bril files found.")
    