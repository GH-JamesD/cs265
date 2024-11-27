import networkx as nx
import matplotlib.pyplot as plt

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
        return build_inlining_tree_from_components(CG, edgelist)

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
        print("Binary Node")
        if tree.left:
            print_counts(tree.left)
        if tree.right:
            print_counts(tree.right)
    elif isinstance(tree, InliningTreeComponentsNode):
        print("Components Node")
        for component in tree.components:
            print_counts(component)


def visualize_inlining_tree(
    tree, 
    parent_label=None, 
    graph=None, 
    pos=None, 
    x=0, 
    y=0, 
    layer_gap=3, 
    node_gap=2, 
    counters=None, 
    width_factor=2
):
    """
    Recursively visualize the inlining tree using matplotlib and networkx, with dynamic horizontal spacing.

    Parameters:
    - tree: The inlining tree to visualize.
    - parent_label: The label of the parent node (None for root).
    - graph: The NetworkX DiGraph object to build the visualization.
    - pos: The positions dictionary for the graph layout.
    - x, y: Coordinates for placing the current node.
    - layer_gap: Vertical gap between tree levels.
    - node_gap: Base horizontal gap between sibling nodes.
    - counters: Dictionary to track unique numbering for each node type.
    - width_factor: Factor to control horizontal spacing dynamically.

    Returns:
    - graph: The updated NetworkX graph.
    - pos: The updated positions dictionary.
    """
    if graph is None:
        graph = nx.DiGraph()
    if pos is None:
        pos = {}
    if counters is None:
        counters = {"Leaf": 0, "Binary": 0, "Components": 0}

    # Assign unique label for the current node
    if isinstance(tree, InliningTreeLeaf):
        counters["Leaf"] += 1
        node_label = f"Leaf {counters['Leaf']}: {len(tree.inlined_edges)} edges"
    elif isinstance(tree, InliningTreeBinaryNode):
        counters["Binary"] += 1
        node_label = f"Binary Node {counters['Binary']}"
    elif isinstance(tree, InliningTreeComponentsNode):
        counters["Components"] += 1
        node_label = f"Components Node {counters['Components']} ({len(tree.components)} components)"
    else:
        node_label = f"Unknown Node"

    # Add the current node to the graph
    graph.add_node(node_label)
    pos[node_label] = (x, -y)
    if parent_label is not None:
        graph.add_edge(parent_label, node_label)

    # Calculate dynamic spacing based on tree structure
    children_count = (
        2 if isinstance(tree, InliningTreeBinaryNode) else len(tree.components)
        if isinstance(tree, InliningTreeComponentsNode)
        else 0
    )
    dynamic_node_gap = node_gap * max(width_factor, children_count)

    # Recursively add child nodes for BinaryNode
    if isinstance(tree, InliningTreeBinaryNode):
        if tree.left:
            visualize_inlining_tree(
                tree.left, node_label, graph, pos, x - dynamic_node_gap, y + layer_gap, layer_gap, node_gap / 1.5, counters, width_factor
            )
        if tree.right:
            visualize_inlining_tree(
                tree.right, node_label, graph, pos, x + dynamic_node_gap, y + layer_gap, layer_gap, node_gap / 1.5, counters, width_factor
            )

    # Recursively add child nodes for ComponentsNode
    elif isinstance(tree, InliningTreeComponentsNode):
        for i, component in enumerate(tree.components):
            child_x = x + (i - (len(tree.components) - 1) / 2) * dynamic_node_gap
            visualize_inlining_tree(
                component, node_label, graph, pos, child_x, y + layer_gap, layer_gap, node_gap / 1.5, counters, width_factor
            )

    return graph, pos

def plot_inlining_tree(tree):
    """
    Visualizes the inlining tree.
    """
    graph, pos = visualize_inlining_tree(tree)
    plt.figure(figsize=(12, 12))
    nx.draw(graph, pos, with_labels=True, node_size=3000, node_color="lightblue", font_size=8, font_weight="bold", arrowsize=15)
    plt.title("Inlining Tree Visualization")
    plt.savefig("inlining_tree.png")
    plt.close()

def plot_call_graph(CG):
    nx.draw(CG, with_labels=True)
    plt.savefig("call_graph.png")
    plt.close()