#!/usr/bin/python3
"""
Compute benchmark results comparing partitioned and unpartitioned SMT checks.
"""
import subprocess
import os
import sys
import re
import csv

def mean_float_dict(dicts, total=False):
    """
    Average the results across the given list of dictionaries.
    """
    if len(dicts) == 0:
        return []
    averaged = dict()
    keys = dicts[0].keys()
    for key in keys:
        newval = []
        for i in range(len(dicts[0][key])):
            sumval = sum([d[key][i] for d in dicts])
            newval.append(sumval / len(dicts))
        # if total is true, sum all the parts together
        if total:
            averaged[key] = sum(newval)
        # otherwise, just return a list of each time that operation was profiled
        else:
            averaged[key] = newval
    return averaged

def join_result_dicts(parted, unparted):
    """
    Join the two dictionaries representing partitioned runs and an unpartitioned run
    into a single dictionary.
    """
    joined = dict()
    for (key, val) in parted.items():
        joined[key + " (parted)"] = val
    joined.update(unparted)
    return joined

def parse_output(output):
    """
    Parse the output of an NV command.
    Returns a dictionary of strings to lists of floats.
    """
    action = re.compile(r"(.*) took: (\d*\.?\d+) secs to complete", re.M)
    z3action = re.compile(r"^\s*:(\w*)\s*(\d*\.?\d+)", re.M)
    # get all the transformation profiling
    profile = dict()
    for match in re.finditer(action, output):
        transform = match.group(1)
        time = float(match.group(2))
        profile.setdefault(transform, list()).append(time)
    # get all the z3 profiling
    for match in re.finditer(z3action, output):
        stat = "z3 " + match.group(1)
        qua = float(match.group(2))
        profile.setdefault(stat, list()).append(qua)
    return profile

def run_command(com, time):
    """
    Run the given command and capture its output.
    If it doesn't finish within the given time, kill it.
    """
    try:
        proc = subprocess.run(com, text=True, check=True, capture_output=True, timeout=time)
        return parse_output(proc.stdout)
    except subprocess.CalledProcessError as exn:
        print(exn.stderr)
        return {}

def run_benchmark(dirformat, nameformat, size, time, trials):
    """
    Run the partitioned and unpartitioned benchmarks in the given directory,
    and return a dictionary of profiling information.
    """
    benchdir = dirformat.format(size)
    nvpath = os.path.join(os.getcwd(), "nv")
    if not os.path.exists(nvpath):
        print("Did not find an 'nv' executable in the current working directory!")
        sys.exit(1)
    # run nv with verbose, SMT and partitioning flags
    com = [nvpath, "-v", "-m", "-k"]
    partf = os.path.join(benchdir, nameformat.format(size, "-part"))
    unpartf = os.path.join(benchdir, nameformat.format(size, ""))
    runs = []
    for i in range(trials):
        print("Running trial " + str(i + 1) + " of " + str(trials))
        partcom = run_command(com + [partf], time)
        unpartcom = run_command(com + [unpartf], time)
        runs.append(join_result_dicts(partcom, unpartcom))
    mean = mean_float_dict(runs, total=True)
    mean["Benchmark"] = benchdir
    return mean

def write_csv(results, path):
    """Write the results dictionaries to a CSV."""
    with open(path, 'w') as csvf:
        writer = csv.DictWriter(csvf, fieldnames=results[0].keys(), restval='error')
        writer.writeheader()
        for result in results:
            writer.writerow(result)

if __name__ == "__main__":
    DIRECTORY = "benchmarks/SinglePrefix/FAT{}"
    SIZES = [4, 8, 10]
    TIMEOUT = 600
    TRIALS = 10
    RUNS = []
    for sz in SIZES:
        print("Running benchmark " + DIRECTORY.format(sz))
        RUNS.append(run_benchmark(DIRECTORY, "sp{}{}.nv", sz, TIMEOUT, TRIALS))
    write_csv(RUNS, "results.csv")