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


def build_inlining_tree(CG, edgelist=None):
    if edgelist is None:
        edgelist = []

    if CG.number_of_edges() == 0:
        return InliningTreeLeaf(edgelist)

    if len(list(nx.weakly_connected_components(CG))) > 1:
        return build_inlining_tree_from_components(CG)

    p_edge = choose_part(CG)

    not_inlined = nx.DiGraph(CG)
    not_inlined.remove_edge(*p_edge)

    inlined = contract(CG, p_edge)

    not_inlined_subtree = build_inlining_tree(not_inlined, edgelist)
    inlined_subtree = build_inlining_tree(inlined, edgelist + [p_edge])

    return InliningTreeBinaryNode(not_inlined_subtree, inlined_subtree, edgelist)


def build_inlining_tree_from_components(CG, edgelist=None):
    components = []
    for component in nx.weakly_connected_components(CG):
        subgraph = CG.subgraph(component).copy()
        components.append(build_inlining_tree(subgraph, edgelist))
    return InliningTreeComponentsNode(components, list(CG.edges))


def choose_part(CG):
    directed_bridges = list(nx.bridges(CG.to_undirected()))
    if directed_bridges:
        return adj_to_least_ecc(CG, directed_bridges)
    else:
        U = max(CG.nodes, key=lambda node: CG.out_degree(node))
        V = min(CG.successors(U), key=lambda node: CG.in_degree(node), default=None)
        return (U, V)


def adj_to_least_ecc(CG, edges):
    eccentricities = nx.eccentricity(CG.to_undirected())
    least_eccentric_node = min(eccentricities, key=eccentricities.get)

    for edge in edges:
        if least_eccentric_node in edge:
            if edge in CG.edges:
                return edge
            else:
                edge = (edge[1], edge[0])
                if edge in CG.edges:
                    return edge
    return edges[0] if edges[0] in CG.edges else (edges[0][1], edges[0][0])

def contract(CG, edge):
    u, v = edge
    new_node_name = f"{u}:{v}"
    
    contracted_graph = nx.DiGraph(CG)
    
    contracted_graph.add_node(new_node_name)
    
    for pred in CG.predecessors(u):
        if pred != v:
            contracted_graph.add_edge(pred, new_node_name)
    for pred in CG.predecessors(v):
        if pred != u:
            contracted_graph.add_edge(pred, new_node_name)
    for succ in CG.successors(u):
        if succ != v:
            contracted_graph.add_edge(new_node_name, succ)
    for succ in CG.successors(v):
        if succ != u:
            contracted_graph.add_edge(new_node_name, succ)
    
    contracted_graph.remove_nodes_from([u, v])
    
    return contracted_graph


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