from collections import defaultdict
import networkx as nx

class InliningTreeLeaf:
    def __init__(self, inlined_edges):
        self.inlined_edges = inlined_edges

class InliningTreeBinaryNode:
    def __init__(self, left, right, inlined_edges):
        self.left = left
        self.right = right
        self.inlined_edges = inlined_edges

class InliningTreeComponentsNode:
    def __init__(self, components, inlined_edges):
        self.components = components
        self.inlined_edges = inlined_edges


def build_inlining_tree(CG, edge_count=None, MAXSELF=2):
    if edge_count is None:
        edge_count = defaultdict(int)

    if CG.number_of_edges() == 0:
        return InliningTreeLeaf(dict(edge_count))

    if len(list(nx.weakly_connected_components(CG))) > 1:
        return build_inlining_tree_from_components(CG, edge_count, MAXSELF)

    part_edge = select_partition_edge(CG)

    edge_count[part_edge] += 1

    if part_edge[0] == part_edge[1] and edge_count[part_edge] >= MAXSELF:
        not_inlined = nx.DiGraph(CG)
        not_inlined.remove_edge(*part_edge)
        not_inlined_subtree = build_inlining_tree(not_inlined, edge_count, MAXSELF)
        return InliningTreeBinaryNode(not_inlined_subtree, None, dict(edge_count))

    not_inlined = nx.DiGraph(CG)
    not_inlined.remove_edge(*part_edge)

    if part_edge[0] == part_edge[1]:
        inlined = nx.DiGraph(CG)
    else:
        inlined = nx.contracted_edge(CG, part_edge, self_loops=False)

    not_inlined_subtree = build_inlining_tree(not_inlined, edge_count, MAXSELF)
    inlined_subtree = build_inlining_tree(inlined, edge_count, MAXSELF)

    return InliningTreeBinaryNode(not_inlined_subtree, inlined_subtree, dict(edge_count))


def build_inlining_tree_from_components(CG, edge_count, MAXSELF):
    components = []
    for component in nx.weakly_connected_components(CG):
        subgraph = CG.subgraph(component).copy()
        components.append(build_inlining_tree(subgraph, edge_count, MAXSELF))
    return InliningTreeComponentsNode(components, dict(edge_count))


def select_partition_edge(CG):
    bridges = list(nx.bridges(CG.to_undirected()))
    if bridges:
        return edge_adjacent_to_least_eccentric_node(CG, bridges)
    else:
        U = max(CG.nodes, key=lambda node: CG.out_degree(node))
        V = min(CG.successors(U), key=lambda node: CG.in_degree(node), default=None)
        return (U, V)


def edge_adjacent_to_least_eccentric_node(CG, edges):
    eccentricities = nx.eccentricity(CG.to_undirected())
    least_ecc = min(eccentricities, key=eccentricities.get)

    for edge in edges:
        if least_ecc in edge:
            return edge
    return edges[0]

def print_counts(tree):
    if isinstance(tree, InliningTreeLeaf):
        print("Inlining Counts at Leaf:", tree.inlined_edges)
    elif isinstance(tree, InliningTreeBinaryNode):
        if tree.left:
            print_counts(tree.left)
        if tree.right:
            print_counts(tree.right)
    elif isinstance(tree, InliningTreeComponentsNode):
        for component in tree.components:
            print_counts(component)


            