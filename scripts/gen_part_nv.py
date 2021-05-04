#!/usr/bin/env python3
"""
gen_part_nv.py [nvfile]
A module for generating spX-part.nv fileoutput from spX.nv files.
"""
import os
import sys
import re
import argparse
import subprocess

# used for constructing the graph
import igraph

# Partition cut types
CUTS = [
    # vertical cut: 2 parts
    "v",
    "vertical",
    # horizontal cut: 3 parts
    "h",
    "horizontal",
    # horizontal cut with all pods separate
    "p",
    "pods",
    # horizontal cut with all spines and pods separate
    "s",
    "spines",
    # full cut with every node in its own partition
    "f",
    "full",
]

# Group
# Core nodes are on the spine, edge nodes are ToR,
# and aggregation nodes are between core and edge nodes
CORE = 0
AGGREGATION = 1
EDGE = 2
NONFAT = -1

# Network types
SP = 0
FATPOL = 1


def to_grp(name):
    if name == "core":
        return CORE
    elif name == "aggregation":
        return AGGREGATION
    elif name == "edge":
        return EDGE
    else:
        return NONFAT


def construct_graph(text, is_fattree):
    """
    Construct a digraph from the given edge and node information.
    """
    g = igraph.Graph(directed=True)
    nodes = find_nodes(text, is_fattree)
    for (v, grp) in nodes:
        g.add_vertex(g=grp)
    edges = find_edges(text, is_fattree)
    g.add_edges(edges)
    # add stable node numbering
    for v in g.vs:
        v["id"] = v.index
    return g


def find_edges(text, is_fattree):
    """Return the edges."""
    if is_fattree:
        pat = (
            r"(\d*)-(\d*); "
            r"\(\*(core|aggregation|edge)-\d*,Serial\d*"
            r" --> (core|aggregation|edge)-\d*,Serial\d*\*\)"
        )
    else:
        pat = r"(\d*)-(\d*); \(\*[\w/,]* --> [\w/,]*\*\)"
    prog = re.compile(pat)
    matches = prog.finditer(text)
    outputs = [(int(m.group(1)), int(m.group(2))) for m in matches]
    outputs.sort()
    return outputs


def find_nodes(text, is_fattree):
    """Return the nodes."""
    if is_fattree:
        pat = r"(core|aggregation|edge)-\d*=(\d*)"
    else:
        pat = r"(\w+)(?:-\d*)?=(\d+)"
    prog = re.compile(pat)
    # find all nodes
    matches = prog.finditer(text)
    vertices = [(int(m.group(2)), to_grp(m.group(1))) for m in matches]
    vertices.sort()
    return vertices


def write_preamble(spname, cut):
    """
    Return the string representation of the preamble.
    """
    vim_modeline = "(* vim: set syntax=ocaml: *)"
    if cut == "v" or cut == "vertical":
        oriented = "Vertically partitioned"
    elif cut == "h" or cut == "horizontal":
        oriented = "Horizontally partitioned"
    elif cut == "p" or cut == "pods":
        oriented = "Partitioned into pods"
    elif cut == "s" or cut == "spines":
        oriented = "Partitioned into pods and individual spines"
    elif cut == "f" or cut == "full":
        oriented = "Fully partitioned"
    else:
        raise Exception("Unexpected cut type")
    file_info = f"(* {oriented} version of {spname} *)"
    generated_by = "(* Automatically generated by gen_part_nv.py *)"
    include_utils = 'include "../../../examples/utils.nv"'
    return "\n".join([vim_modeline, file_info, generated_by, include_utils])


def write_partition_str(partitions):
    """
    Return the string representation of the partition function.
    """
    output = "let partition node = match node with\n"
    for i, nodes in enumerate(partitions):
        output += "\n".join([f"  | {node}n -> {i}" for node in nodes]) + "\n"
    return output


def write_interface_str(edges, net_type):
    """
    Return the string representation of the interface function.
    """
    output = "let interface edge x ="
    output += """
  let hasOnlyBgp f =
    x.selected = Some 3u2 && (match x.bgp with
      | Some b -> f b
      | None -> false)
  in"""
    if net_type == FATPOL:
        output += """
  let ignoreBgp = match x.bgp with
    | Some b -> ignore b.comms
    | None -> true
  in"""
        default = "match x.bgp with | Some b -> ignore b.comms | None -> true"
    elif net_type == SP:
        default = "true"
    else:
        raise Exception("Unexpected net type")
    output += "\n  match edge with\n"
    for (start, end) in edges:
        if net_type == SP:
            fn = "(fun b -> true)"
        elif net_type == FATPOL:
            fn = "(fun b -> ignore b.comms)"
        output += f"  | {start}~{end} -> hasOnlyBgp {fn}\n"
    output += f"  | _ -> {default}\n"
    return output


def get_net_type(root):
    if root.startswith("sp"):
        net_type = SP
    elif root.startswith("fat"):
        net_type = FATPOL
    else:
        net_type = NONFAT
    return net_type


def get_part_fname(nvfile, cut, simulate):
    """
    Return the name of the partition file for the corresponding nv file,
    and the network type.
    """
    spdir, spname = os.path.split(nvfile)
    root, nvext = os.path.splitext(spname)
    net_type = get_net_type(root)
    # mark simulated solutions with an x for exact
    sim = "-x" if simulate else ""
    prefix = f"{root}-{cut}{sim}"
    partfile = os.path.join(spdir, prefix + nvext)
    suffix = 1
    # don't overwrite an existing path: instead, create a new file
    while os.path.exists(partfile):
        partfile = os.path.join(spdir, prefix + str(suffix) + nvext)
        suffix += 1
    return partfile, net_type


def nodes_cut_fully(graph, dest):
    """
    Return the nodes divided up fully into separate partitions.
    Order is established by BFS.
    """
    return [[v["id"]] for v in graph.bfsiter(dest)]


def nodes_cut_spines(graph, dest):
    """
    Return the nodes divided up such that the destination's pod
    is in one partition, the spine nodes are each in another
    and the other pod nodes are each in another.
    """
    podgraph = graph.subgraph(graph.vs.select(g_ne=CORE))
    pods = podgraph.decompose()
    dest_idx = 0
    for (i, pod) in enumerate(pods):
        if dest in pod.vs["id"]:
            dest_idx = i
    spines = [v["id"] for v in graph.vs.select(g_eq=CORE)]
    nondest_pods = [list(pod.vs["id"]) for pod in pods]
    dest_pod = nondest_pods.pop(dest_idx)
    dest_pod.sort()
    spines.sort()
    for pod in nondest_pods:
        pod.sort()
    return [dest_pod] + [[s] for s in spines] + nondest_pods


def nodes_cut_pods(graph, dest):
    """
    Return the nodes divided up such that the destination's pod
    is in one partition, the spine nodes are in another and the
    other pod nodes are each in another.
    """
    podgraph = graph.subgraph(graph.vs.select(g_ne=CORE))
    pods = podgraph.decompose()
    dest_idx = 0
    for (i, pod) in enumerate(pods):
        if dest in pod.vs["id"]:
            dest_idx = i
    spines = [v["id"] for v in graph.vs.select(g_eq=CORE)]
    nondest_pods = [list(pod.vs["id"]) for pod in pods]
    dest_pod = nondest_pods.pop(dest_idx)
    dest_pod.sort()
    spines.sort()
    for pod in nondest_pods:
        pod.sort()
    return [dest_pod, spines] + nondest_pods


def nodes_cut_horizontally(graph, dest):
    """
    Return the nodes divided up such that the destination's pod
    is in one partition, the spine nodes are in another and the
    other pod nodes are in a third.
    """
    podgraph = graph.subgraph(graph.vs.select(g_ne=CORE))
    pods = podgraph.decompose()
    dest_pod = []
    nondest_pods = []
    for pod in pods:
        if dest in pod.vs["id"]:
            dest_pod = [v["id"] for v in pod.vs]
        else:
            nondest_pods += [v["id"] for v in pod.vs]
    spines = [v["id"] for v in graph.vs.select(g_eq=CORE)]
    dest_pod.sort()
    spines.sort()
    nondest_pods.sort()
    return dest_pod, spines, nondest_pods


def nodes_cut_vertically(graph, dest):
    """
    Return the nodes divided up such that half of the spine
    nodes and half of the pods are in one partition
    and the others are in another.
    """
    spines = [v for v in graph.vs.select(g_eq=CORE)]
    half_spines = spines[: (len(spines) // 2)]
    aggs = [v for v in graph.vs.select(g_eq=AGGREGATION)]
    half_aggs = aggs[: (len(aggs) // 2)]
    # use a set so as not to add twice
    pods = set()
    for v in half_aggs:
        pods.add(v.index)
        for u in v.neighbors():
            if u["g"] == EDGE:
                pods.add(u.index)
    # return half of the spines along with the pods
    group1 = [x.index for x in half_spines] + list(pods)
    # get all nodes not in group1
    all_nodes = set(x.index for x in graph.vs)
    group2 = [x for x in all_nodes.difference(set(group1))]
    group1.sort()
    group2.sort()
    if dest in group1:
        return group1, group2
    else:
        return group2, group1


def get_cross_edges(graph, partitions, ranked=False):
    """
    Get the edges in the network which go between partitions.
    If ranked is True, only include edges which go from lower-ranked partitions
    to higher-ranked partitions.
    These edges are used to determine the interface functions.
    """
    # construct a map of nodes to their partitions
    n_parts = {node: i for (i, part) in enumerate(partitions) for node in part}

    def edge_predicate(e):
        src = n_parts[e.source]
        tgt = n_parts[e.target]
        return (ranked and src < tgt) or (not ranked and src != tgt)

    return [e.tuple for e in graph.es if edge_predicate(e)]


def get_vertical_cross_edges(graph, partitions, dest):
    all_cross = get_cross_edges(graph, partitions, ranked=True)
    updated = []
    for e in all_cross:
        # prune non-destination-pod cross edges
        node = graph.vs[e[0]]
        neighbors = [v["id"] for v in node.neighbors()]
        if node["g"] == AGGREGATION and dest not in neighbors:
            continue
        else:
            updated.append(e)
    return updated


def cut_nodes(graph, dest, cut):
    """
    Cut the graph's nodes into a list of list of nodes in partition rank order,
    based on the given destination (always in the 0th partition) and the type
    of cut desired.
    """
    if cut == "vertical" or cut == "v":
        nodes = nodes_cut_vertically(graph, dest)
    elif cut == "horizontal" or cut == "h":
        nodes = nodes_cut_horizontally(graph, dest)
    elif cut == "pods" or cut == "p":
        nodes = nodes_cut_pods(graph, dest)
    elif cut == "spines" or cut == "s":
        nodes = nodes_cut_spines(graph, dest)
    elif cut == "full" or cut == "f":
        nodes = nodes_cut_fully(graph, dest)
    else:
        raise Exception("Unexpected cut type")
    return nodes


def split_prefooter(text):
    """
    Return all program text before and after the declaration of
    the fattree node types, split into two.
    """
    prog = re.compile(r"\(\* {((edge|core|aggregation)-\d+=\d+,?\s*)*}\*\)")
    match = prog.search(text)
    end = match.end()
    return (text[: end + 1], text[end + 1 :])


def parse_sim(output):
    """Parse the nv simulator solution."""
    pat = re.compile(r"Node (\d+)\n-*\n((?:.|\n)+?)\n\n", re.M)
    return dict((int(m.group(1)), m.group(2)) for m in pat.finditer(output))


def format_fatPol_sols(sols, atype):
    """
    Parse the printed solution for a fatPol benchmark and
    return a correctly-formatted NV attribute.
    """

    def record_to_str(d):
        return "{" + "; ".join([f"{k}={v}" for k, v in d.items()]) + "}"

    ribpat = re.compile(r"(\w*)= (Some\(((?:.|\n)*?)\)|None);", re.M)
    bgppat = re.compile(r"(\w*)= (\d*u\d*|{ (?:\d*u32 \|-> true\n?)* });", re.M)
    commslines = re.compile(r"\n", re.M)
    commspat = re.compile(r"(\d*u32) \|-> true", re.M)
    new_sols = dict()
    for k, v in sols.items():
        # parse the RIB
        rib = dict()
        rib = dict(m.group(1, 3) for m in ribpat.finditer(v))
        bgpsol = rib.get("bgp")
        if bgpsol is not None:
            bgp = dict(m.group(1, 2) for m in bgppat.finditer(bgpsol))
            commssol = bgp.get("comms")
            if commssol is not None:
                oneline = commslines.sub(r", ", commssol)
                bgp["comms"] = commspat.sub(r"\1", oneline)
            rib["bgp"] = f"{record_to_str(bgp)}"
        # Add Some wrapper as needed for rib components
        rib = dict(
            (k, f"Some({v})" if v is not None else f"{v}") for k, v in rib.items()
        )
        new_sols[k] = record_to_str(rib)
    return new_sols


def run_nv_simulate(path):
    """ Run nv's simulation tool and capture its output. """
    nvpath = os.path.join(os.getcwd(), "nv")
    if not os.path.exists(nvpath):
        print("Did not find 'nv' executable in the current working directory")
        sys.exit(1)
    args = [nvpath, "-v", "-s"] + [path]
    print(f"Running {' '.join(args)}")
    try:
        proc = subprocess.run(args, text=True, check=True, capture_output=True)
        return parse_sim(proc.stdout)
        # return format_fatPol_sols(parse_sim(proc.stdout))
    except subprocess.CalledProcessError as exn:
        print(exn.stderr)
        return {}
    except subprocess.TimeoutExpired as exn:
        print(exn.stderr)
        return {}


def write_interface_from_sim(edges, solution):
    """
    Write an interface string based on the given simulation.
    """
    output = "let interface edge a =\n  match edge with\n"
    for (start, end) in edges:
        sol = solution[start]
        output += f"  | {start}~{end} -> a = {sol}\n"
    return output


# TODO: make the dest optional if simulate is True
def gen_part_nv(nvfile, dest, cut, simulate=True, verbose=False):
    """Generate the partition file."""
    part, net_type = get_part_fname(nvfile, cut, simulate)
    if verbose:
        print("Outfile: " + part)
    if simulate:
        # generate the solution from simulation
        solution = run_nv_simulate(nvfile)
        if verbose:
            print("Simulated " + nvfile)
    with open(nvfile, "r") as inputfile:
        text = inputfile.read()
    # compute the graph topology
    graph = construct_graph(text, net_type != NONFAT)
    if verbose:
        print(str(graph))
    # get the three parts
    preamble = write_preamble(os.path.basename(nvfile), cut)
    # include_sp, footer = split_prefooter(text)
    nodes = cut_nodes(graph, dest, cut)
    # get the cross edges
    if simulate:
        edges = get_cross_edges(graph, nodes, ranked=False)
    elif net_type == FATPOL and (cut == "vertical" or cut == "v"):
        # special case for handling vertical cuts
        edges = get_vertical_cross_edges(graph, nodes, dest)
    else:
        edges = get_cross_edges(graph, nodes, ranked=True)
    if verbose:
        print(nodes)
        print([e for e in edges])
    partition = write_partition_str(nodes)
    if simulate:
        interface = write_interface_from_sim(edges, solution)
    else:
        interface = write_interface_str(edges, net_type)
    # perform the decomposed transfer on the input side
    repl = (
        r"solution { init = init; trans = trans; merge = merge;"
        r" interface = interface; rtrans = trans }"
    )
    # include_sp = re.sub(r"solution {.*}", repl, include_sp)
    # footer = re.sub(r"solution {.*}", repl, footer)
    text = re.sub(r"solution {.*}", repl, text)
    # put 'em all together
    output = "\n".join([preamble, text, partition, interface])
    with open(part, "w") as outfile:
        outfile.write(output)
    print(f"Saved network to {part}")


def print_graph(nvfile):
    """Print the associated graph for the given NV file."""
    _, spname = os.path.split(nvfile)
    root, _ = os.path.splitext(spname)
    net_type = get_net_type(root)
    with open(nvfile, "r") as inputfile:
        text = inputfile.read()
    # compute the graph topology
    graph = construct_graph(text, net_type != NONFAT)
    print(str(graph))
    # adj = graph.get_adjlist(mode="all")
    # assert all([len(l) % 2 == 0 for l in adj])


class ParseFileDest(argparse.Action):
    """
    An argparse parser for collecting files paired with their destination.
    """

    def __call__(self, parser, namespace, values, option_string=None):
        setattr(namespace, self.dest, dict())
        for value in values:
            try:
                f, d = value.split(":")
                getattr(namespace, self.dest)[f] = int(d)
            except ValueError:
                break

    def format_usage():
        return "file.nv:node"


def parser():
    parser = argparse.ArgumentParser(
        description="Generate partitioned versions of network benchmarks."
    )
    parser.add_argument(
        "files",
        nargs="+",
        action=ParseFileDest,
        help='unpartitioned network files with their unique associated \
        destination nodes, separated by a colon, e.g. "simple.nv:0"',
    )
    parser.add_argument(
        "-c",
        "--cuts",
        required=True,
        nargs="+",
        choices=CUTS,
        help="types of cut across the network topology",
    )
    parser.add_argument(
        "-s",
        "--simulate",
        action="store_true",
        help="generate interface by simulating the given benchmark",
    )
    parser.add_argument(
        "-v", "--verbose", action="store_true", help="increase verbosity"
    )
    parser.add_argument(
        "-p",
        "--print",
        action="store_true",
        help="print topology info instead of generating partition",
    )
    return parser


def main():
    args = parser().parse_args()
    for (file, dest) in args.files.items():
        if args.print:
            print_graph(file)
        else:
            for cut in args.cuts:
                gen_part_nv(file, dest, cut, verbose=args.verbose)


if __name__ == "__main__":
    main()