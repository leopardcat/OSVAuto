"""
This file contains various utility functions.
"""

from collections import defaultdict, deque


def indent(s: str, n: int = 2) -> str:
    """Indent each line by a number of spaces.
    
    Parameters
    ----------
    s : str
        Input string
    n : int, default = 2
        Number of spaces to prepend before each line of s.

    """
    lines = s.split('\n')
    return '\n'.join(' ' * n + line for line in lines)

def short_form(s: str, threshold: int = 30) -> str:
    """Obtain the short form of a string."""
    s = s.replace('\n', '').replace('  ', ' ')
    if len(s) > threshold:
        return s[:threshold] + " ... "
    else:
        return s

def extract_parts(var_name: str) -> tuple[str, int]:
    """Extract alphabetical and number part of var_name."""
    letters = ""
    number = 0
    number_str = ""
    
    # Traverse the string from the end to the beginning
    for i in range(len(var_name) - 1, -1, -1):
        if var_name[i].isdigit():
            number_str = var_name[i] + number_str
        else:
            letters = var_name[:i + 1]
            break
    
    # Convert the number part to an integer, if any
    if number_str:
        number = int(number_str)
    
    return letters, number

def variant_names(names: set[str], var_name: str) -> str:
    """Obtain a variant of prefix that is not in the set names.
    
    Parameters
    ----------
    names : Set[str]
        Names to avoid, usually the set of existing variables.
    var_name : str
        Suggested name, the returned name will be based on this.

    """
    if var_name not in names:
        return var_name
    prefix, number = extract_parts(var_name)
    while True:
        if prefix + str(number) not in names:
            return prefix + str(number)
        number += 1

def topological_sort(graph: dict[int, list[int]]) -> list[int]:
    """Perform topological sort on the graph.
    
    Input is the adjacency list representation of the graph.

    The returned order satisfies the condition that for all edges `i -> j`
    in the graph, node `i` occurs before `j` in the order.

    """
    # Create a dictionary to store the in-degree of each vertex
    in_degree = defaultdict(int)
    
    # Initialize the in-degree of each vertex
    for node in graph:
        if node not in in_degree:
            in_degree[node] = 0
        for neighbor in graph[node]:
            in_degree[neighbor] += 1
    
    # Create a queue and enqueue all vertices with in-degree 0
    queue = deque([node for node in in_degree if in_degree[node] == 0])
    
    # List to store the topological order
    topo_order = []
    
    while queue:
        # Dequeue a vertex from the queue
        node = queue.popleft()
        topo_order.append(node)
        
        # Decrease the in-degree of all its neighbors by 1
        for neighbor in graph[node]:
            in_degree[neighbor] -= 1
            # If in-degree of a neighbor becomes 0, add it to the queue
            if in_degree[neighbor] == 0:
                queue.append(neighbor)
    
    # If the length of the topological order is not equal to the number of vertices,
    # then the graph contains a cycle and topological sorting is not possible
    if len(topo_order) != len(graph):
        raise ValueError("The graph contains a cycle, topological sorting is not possible.")
    
    return topo_order
