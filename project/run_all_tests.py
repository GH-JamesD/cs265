import os
import subprocess
import numpy as np
from matplotlib import pyplot as plt
import pandas as pd
import concurrent.futures
from tqdm import tqdm

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

def run_command(bril_file, command_template):
    """Run the specified command on a single .bril file."""
    command = command_template.format(file=bril_file)
    try:
        print(f"Running command: {command}")
        result = subprocess.check_output(command, shell=True, timeout=600, text=True)
        return bril_file, result
    except Exception as e:
        print(f"Error while running command on {bril_file}, stopping it now: {e}")
        return bril_file, None

def run_commands_multithreaded(bril_files, command_template):
    """Run the specified command on each .bril file using multithreading."""
    results = []
    with concurrent.futures.ThreadPoolExecutor() as executor:
        futures = [executor.submit(run_command, bril_file, command_template) for bril_file in bril_files]
        for future in tqdm(concurrent.futures.as_completed(futures), total=len(futures)):
            try:
                results.append(future.result())
            except Exception as e:
                print(f"Error during execution: {e}")
    return results

if __name__ == "__main__":
    directory_to_search = "../../bril/benchmarks/"

    bench_cmds = dict(
        no_recursion = "cat {file} | bril2json | python inlining.py 0",
        depth_1 = "cat {file} | bril2json | python inlining.py 1",
        depth_2 = "cat {file} | bril2json | python inlining.py 2"
    )

    bril_files = find_bril_files(directory_to_search)

    res_dict = {}

    analyses = dict(
        # total_len = "python count_instrs.py",
        # loop_loc = "python count_loop_loc.py",
    )

    if bril_files:
        print(f"Found {len(bril_files)} .bril files.")
        out = dict(
            benchmark = [],
            run = [],
            baseline = [],
            best = [],
            results = []
        )

        for title, cmd in bench_cmds.items():
            results = run_commands_multithreaded(bril_files, cmd)

            for bril_file, output in results:
                if "conjugate-gradient" in bril_file.split("/")[-1].split(".")[0]:
                    continue

                out["benchmark"].append(bril_file.split("/")[-1].split(".")[0])
                out["run"].append(title)

                if output is None:
                    out["baseline"].append(None)
                    out["best"].append(None)
                    out["results"].append(None)
                else:
                    output = output.split("\n")
                    out["baseline"].append(output[0])
                    out["best"].append(output[-2])
                    out["results"].append(output[:-1])

        df = pd.DataFrame(out, columns=out.keys())
        df.to_csv("tests_autotune.csv", index=False)
    else:
        print("No .bril files found.")
