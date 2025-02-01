"""Classification graph for instantiation."""

from typing import Iterable, Optional
from queue import Queue
import z3

from osverify import os_struct
from osverify import os_term
from osverify.os_term import OSTerm, OSVar
from osverify.os_theory import OSTheory
from osverify import os_z3wrapper
from osverify import os_match
from osverify import os_simplify
from osverify import os_query


def filter_cond(cond: OSTerm) -> bool:
    """Filter condition to be processed."""
    if not isinstance(cond, os_term.OSOp):
        return False
    if cond.op in ("&&", "||", "->"):
        t1, t2 = cond.args
        return filter_cond(t1) and filter_cond(t2)
    if cond.op == "!":
        return filter_cond(cond.args[0])
    if cond.op not in ("<=", ">=", "==", "!=", "<", ">"):
        return False
    t1, t2 = cond.args
    if not os_struct.is_num_type(t1.type):
        return False
    return True


class GraphNode:
    pass

class QuantifierNode(GraphNode):
    """Quantifier nodes.
    
    They correspond to quantified variables in some assumption. Each
    quantified variable must have integer/bitvector type.

    Attributes
    ----------
    assume_name : str
        name of the assumption.
    var : OSVar
        quantified variable, including its name and type.

    """
    def __init__(self, assume_name: str, var: OSVar):
        self.assume_name = assume_name
        self.var = var

    def __str__(self):
        return f"({self.assume_name}, {self.var})"

    def __repr__(self):
        return f"QuantifierNode({self.assume_name}, {self.var})"

    def __eq__(self, other):
        return isinstance(other, QuantifierNode) and \
            self.assume_name == other.assume_name and self.var == other.var

    def __hash__(self):
        return hash(("QuantifierNode", self.assume_name, self.var))

class SeqNode(GraphNode):
    """Sequence nodes, correspond to free sequence terms in the state.
    
    Attributes
    ----------
    seq_t : OSTerm
        corresponding term, must be free and has sequence type.

    """
    def __init__(self, seq_t: OSTerm):
        self.seq_t = seq_t

    def __str__(self):
        return f"[{self.seq_t}]"
    
    def __repr__(self):
        return f"SeqNode({self.seq_t})"

    def __eq__(self, other):
        return isinstance(other, SeqNode) and self.seq_t == other.seq_t

    def __hash__(self):
        return hash(("SeqNode", self.seq_t))

class MapNode(GraphNode):
    """Map nodes, correspond to free map terms in the state.
    
    Attributes
    ----------
    map_t : OSTerm
        corresponding term, must be free and has map type.

    """
    def __init__(self, map_t: OSTerm):
        self.map_t = map_t

    def __str__(self):
        return f"{{{self.map_t}}}"
    
    def __repr__(self):
        return f"MapNode({self.map_t})"

    def __eq__(self, other):
        return isinstance(other, MapNode) and self.map_t == other.map_t

    def __hash__(self):
        return hash(("MapNode", self.map_t))

class Edge:
    """Represents a directed edge in the classification graph.

    The edge `i -(weight)-> a`, where `i` is a `QuantifierNode` and
    `a` is a `SeqNode`, indicates the presence of a term `a[i+weight]`
    in the forall expression with quantifier `i`. This indicates
    that:
    - if `i` is given instantiation `c`, then `a` should be instantiated
      with `c + weight`.
    - if `a` is given instantiation `c`, then `i` should be instantiated
      with `c - weight`, subject to the (optional) condition on the edge
      is satisfied.

    A list of conditions `conds` may be optionally added, to specify
    the condition 
    
    """
    def __init__(self, source: GraphNode, target: GraphNode, weight: OSTerm,
                 generation: int, *,
                 conds: Iterable[OSTerm] = tuple()):
        self.source = source
        self.target = target
        self.weight = weight
        self.generation = generation
        self.conds = tuple(conds)

    def print(self, print_conds=True):
        if self.conds and print_conds:
            cond_str = "[" + ", ".join(str(cond) for cond in self.conds) + "] ==> "
        else:
            cond_str = ""
        return f"{cond_str}{self.source} -({self.weight})-> {self.target}"
    
    def __str__(self):
        return self.print(print_conds=True)

    def __repr__(self):
        return f"Edge({self.source}, {self.target}, {self.weight}, {self.conds})"
    
    def __eq__(self, other):
        return isinstance(other, Edge) and self.source == other.source and \
            self.target == other.target and self.weight == other.weight and \
            self.generation == other.generation and self.conds == other.conds
    
    def shadows(self, other: "Edge"):
        """Perform simple shadowing check: an edge shadows another if the condition
        is a subset of the condition in other.
        
        """
        return self.source == other.source and self.target == other.target and \
            self.weight == other.weight and self.generation <= other.generation and \
            all(cond in other.conds for cond in self.conds)


class ConditionalTerm:
    """Represents a term with conditions.
    
    Intuitively, `ConditionalTerm(conds, gen, t)` means a subterm `t` that is
    located under conditions in `conds`. For example,

    - in the term `c -> t`, the subterm `t` has condition `c`.
    - in the term `if (cond) { t1 } else { t2 }`, the term `t1` has condition
      `cond` while the term `t2` has condition `!cond`.
    
    The generation number is interpreted as follows:
    - 0 for terms that come from the original state.
    - n + 1 for terms that come from instantiations of generation n.

    Attributes
    ----------
    conds : tuple[OSTerm]
        set of conditions.
    generation : int
        generation number

    """
    def __init__(self, conds: Iterable[OSTerm], generation: int, t: OSTerm):
        self.conds = tuple(conds)
        self.generation = generation 
        self.t = t

    def __str__(self):
        return "[" + ", ".join(str(cond) for cond in self.conds) + "] ==> " + str(self.t)

    def __repr__(self):
        return f"ConditionalTerm({repr(self.conds)}, {self.generation}, {repr(self.t)})"

    def __eq__(self, other):
        return isinstance(other, ConditionalTerm) and \
            self.conds == other.conds and self.generation == other.generation and \
            self.t == other.t
    
    def __hash__(self):
        return hash(("ConditionalTerm", self.conds, self.t))

    def shadows(self, other: "ConditionalTerm"):
        """Perform simple shadowing check: a conditional term shadows another if
        the condition is a subset of the condition in other.
        
        """
        return self.t == other.t and self.generation <= other.generation and \
            all(cond in other.conds for cond in self.conds)


def get_new_conds(inst: OSTerm, var: Optional[OSVar],
                  edge_conds: tuple[OSTerm]) -> tuple[OSTerm]:
    """Instantiate edge_conds with var -> inst."""
    if var is None:
        return edge_conds

    res: list[OSTerm] = []
    for cond in edge_conds:
        # Coerce instantiation to be the same type as var if necesary
        if os_struct.is_bv_type(var.type) and inst.type == os_struct.Int:
            new_inst = os_term.convert_bitvector(inst, var.type)
        else:
            new_inst = inst
        conds = os_term.split_conj(cond.subst({var.name: new_inst}))
        for cond in conds:
            if cond not in res:
                res.append(cond)
    return tuple(res)

class ClassificationGraph:
    """Classification graph.
    
    Each node in the graph corresponds to either quantifier, sequence,
    or map nodes.

    Non-free quantifier nodes are those quantified variables `i` satisfying
    the following condition:
    - In some term of the form `seq_index(n, seq)`, `seq` is non-free,
      variable `i` appears in `n`, and `i` does not appear in `seq`. This
      means instantiation for `i` should wait until the bound variables
      in `seq` are instantiated.
    - Likewise for `indom(k, map)` and `get(k, map)`.

    """
    def __init__(self, thy: OSTheory, *, parent: Optional["ClassificationGraph"] = None):
        self.thy = thy
        self.parent = parent

        # Z3 solver object and conversion context
        self.solver = z3.Solver()
        self.convert_ctxt = os_z3wrapper.Z3ConvertContext()
        if self.parent:
            for basic_cond in self.parent.get_all_basic_conds():
                self.solver.add(os_z3wrapper.convert(self.thy, basic_cond, self.convert_ctxt))

        # Frame count
        self.frame = 0 if self.parent is None else self.parent.frame + 1

        self.nodes: list[GraphNode] = list()
        self.edges: dict[GraphNode, list[Edge]] = dict()
        self.seq_patterns: dict[SeqNode, list[Edge]] = dict()
        self.map_patterns: dict[MapNode, list[Edge]] = dict()

        # Additional instantiations for each quantifier node. This will be
        # added only for new quantifier nodes in the graph.
        self.index_inst: dict[QuantifierNode, list[OSTerm]] = dict()

        # List of instantiations
        self.node_inst: dict[GraphNode, list[ConditionalTerm]] = dict()

        # List of basic conditions
        self.basic_conds: list[OSTerm] = list()

        # Mapping from quantifier node to the term to be instantiated.
        # The term should contain the variable.
        self.term_map: dict[QuantifierNode, OSTerm] = dict()
        self.assume_map: dict[QuantifierNode, os_query.Assumes] = dict()

        # Current queue of instantiations
        self.to_visit: Queue[tuple[GraphNode, ConditionalTerm]] = Queue()

    def get_all_nodes(self) -> list[GraphNode]:
        """Obtain all nodes for the current graph."""
        res: list[GraphNode] = self.parent.get_all_nodes() if self.parent else []
        res.extend(self.nodes)
        return res
    
    def get_all_edges(self, node: GraphNode) -> list[Edge]:
        """Obtain all edges for the current graph."""
        res: list[Edge] = self.parent.get_all_edges(node) if self.parent else []
        if node in self.edges:
            res.extend(self.edges[node])
        return res
    
    def get_all_seq_patterns(self, node: SeqNode) -> list[Edge]:
        """Obtain all sequence patterns."""
        res: list[Edge] = self.parent.get_all_seq_patterns(node) if self.parent else []
        if node in self.seq_patterns:
            res.extend(self.seq_patterns[node])
        return res
    
    def get_all_map_patterns(self, node: MapNode) -> list[Edge]:
        """Obtain all map patterns."""
        res: list[Edge] = self.parent.get_all_map_patterns(node) if self.parent else []
        if node in self.map_patterns:
            res.extend(self.map_patterns[node])
        return res
    
    def get_all_node_insts(self, node: GraphNode) -> list[ConditionalTerm]:
        """Obtain list of all node instantiations."""
        insts: list[ConditionalTerm] = self.parent.get_all_node_insts(node) if self.parent else []
        if node in self.node_inst:
            insts.extend(self.node_inst[node])
        return insts

    def get_all_basic_conds(self) -> list[OSTerm]:
        """Obtain list of all basic conditions."""
        res: list[OSTerm] = self.parent.get_all_basic_conds() if self.parent else []
        res.extend(self.basic_conds)
        return res

    def get_term_map(self, node: QuantifierNode) -> OSTerm:
        if node in self.term_map:
            return self.term_map[node]
        if not self.parent:
            raise AssertionError(f"get_term_map: node {node} is not mapped")
        return self.parent.get_term_map(node)

    def get_assume_map(self, node: QuantifierNode) -> os_query.Assumes:
        if node in self.assume_map:
            return self.assume_map[node]
        if not self.parent:
            raise AssertionError(f"get_term_map: node {node} is not mapped")
        return self.parent.get_assume_map(node)

    def add_basic_conds(self, cond: OSTerm):
        """Add basic condition."""
        if not os_term.is_forall(cond) and cond not in self.get_all_basic_conds() and \
            filter_cond(cond):
            self.basic_conds.append(cond)
            self.solver.add(os_z3wrapper.convert(self.thy, cond, self.convert_ctxt))

    def check_basic_conds(self) -> bool:
        """Return true if the basic conditions already result in contradiction."""
        res = self.solver.check()
        return str(res) == "unsat"

    def add_node(self, node: GraphNode):
        """Add a node to the classification graph.
        
        If the node already exists in the graph, no change is made.

        """
        if node in self.get_all_nodes():
            return
        self.nodes.append(node)
        if isinstance(node, QuantifierNode):
            self.index_inst[node] = list()

        # Propagate sequence nodes with same name
        if isinstance(node, SeqNode) and self.parent:
            for old_node in self.parent.seq_nodes():
                t1, t2 = node.seq_t, old_node.seq_t
                t1_name, t1_idx = os_term.dest_atomic_term(t1)
                t2_name, t2_idx = os_term.dest_atomic_term(t2)
                if t1 != t2 and t1_name == t2_name and len(t1_idx) == len(t2_idx):
                    eq_conds = [os_term.eq(id1, id2) for id1, id2 in zip(t1_idx, t2_idx)]
                    for ct in self.parent.get_all_node_insts(old_node):
                        self.add_node_inst(node, ct.t, ct.generation, cur_conds=ct.conds, edge_conds=eq_conds)

        if isinstance(node, MapNode) and self.parent:
            for old_node in self.parent.map_nodes():
                t1, t2 = node.map_t, old_node.map_t
                t1_name, t1_idx = os_term.dest_atomic_term(t1)
                t2_name, t2_idx = os_term.dest_atomic_term(t2)
                if t1 != t2 and t1_name == t2_name and len(t1_idx) == len(t2_idx):
                    eq_conds = [os_term.eq(id1, id2) for id1, id2 in zip(t1_idx, t2_idx)]
                    for ct in self.parent.get_all_node_insts(old_node):
                        self.add_node_inst(node, ct.t, ct.generation, cur_conds=ct.conds, edge_conds=eq_conds)

    def add_term_map(self, assume: os_query.Assumes, var: OSVar, t: OSTerm):
        """Add mapping from quantifier node to its corresponding term."""
        node = QuantifierNode(assume.name, var)
        if node in self.term_map:
            raise AssertionError(f"add_term_map: node {node} is already mapped")
        self.term_map[node] = t
        self.assume_map[node] = assume

    def add_edge_internal(self, edge: Edge):
        """Internal function for adding an edge."""
        all_edges = self.get_all_edges(edge.source)
        for old_edge in all_edges:
            if old_edge.shadows(edge):
                return

        if edge.source not in self.edges:
            self.edges[edge.source] = list()
        self.edges[edge.source].append(edge)

        # If there are already instantiations for source in parent,
        # perform propagation across this edge.
        if self.parent:
            for ct in self.parent.get_all_node_insts(edge.source):
                self.propagate_edge(edge, ct)

    def add_edge(self, source: GraphNode, target: GraphNode, weight: OSTerm,
                 generation: int, *, conds: Iterable[OSTerm] = tuple()):
        """Add edge with given weight from source to target.
        
        This function adds edge in *both* directions. The reverse direction
        has weight negated.

        """
        edge = Edge(source, target, weight, generation, conds=tuple(conds))
        edge_inv = Edge(target, source, os_term.get_uminus(weight), generation, conds=conds)
        self.add_edge_internal(edge)
        self.add_edge_internal(edge_inv)

    def add_pattern_edge(self, source: GraphNode, target: GraphNode, expr: OSTerm,
                         generation: int, *, conds: Iterable[OSTerm] = tuple()):
        """Add edge corresponding to given expression.
        
        Assume source is a sequence or map node, target is a quantifier node.
        This edge indicates that the sequence or map node is accessed by
        a pattern containing the quantifier node.

        Here expr is the expression to be matched (assumed to be already
        in schematic form). This function adds only the edge from source
        (sequence or map node) to target (quantifier node).
        
        """
        assert isinstance(target, QuantifierNode)
        edge = Edge(source, target, expr, generation, conds=tuple(conds))
        if isinstance(source, SeqNode):
            all_seq_patterns = self.get_all_seq_patterns(source)
            for old_pattern in all_seq_patterns:
                if old_pattern.shadows(edge):
                    return
            if source not in self.seq_patterns:
                self.seq_patterns[source] = list()
            self.seq_patterns[source].append(edge)
        elif isinstance(source, MapNode):
            all_map_patterns = self.get_all_map_patterns(source)
            for old_pattern in all_map_patterns:
                if old_pattern.shadows(edge):
                    return
            if source not in self.map_patterns:
                self.map_patterns[source] = list()
            self.map_patterns[source].append(edge)

    def add_index_inst(self, node: QuantifierNode, weight: OSTerm):
        """Add an index instantiation for index node with given weight.
        
        This function is invoked for each occurrence of i + n <= m or
        m <= i + n, then m - n is added as an index instantiation for
        index i.
        
        """
        if node not in self.index_inst:
            self.index_inst[node] = list()
        self.index_inst[node].append(weight)

    def add_node_inst(self, target: GraphNode, inst: OSTerm, generation: int, *,
                      cur_conds: tuple[OSTerm] = tuple(),
                      var: Optional[OSVar] = None,
                      edge_conds: tuple[OSTerm] = tuple(),
                      verbose=False):
        """Add instantiation `inst` to `target`.
        
        `cur_conds` is the list of conditions associated to the current
        instantiation. The new instantiation has conditions that is the
        combination of `cur_conds` and `edge_conds` (instantiated by
        substituting `inst` for variable `var`).

        """
        # Construct the set of new conditions and ConditionalTerm 
        new_conds = list(cur_conds)
        if inst.type == os_struct.Int:
            inst = os_simplify.normalize_arith(inst)
        for cond in get_new_conds(inst, var, edge_conds):
            if cond not in new_conds:
                new_conds.append(cond)
        new_ct = ConditionalTerm(new_conds, generation, inst)

        # Simple test of existence
        for old_ct in self.get_all_node_insts(target):
            if old_ct.shadows(new_ct):
                return False

        # Check if there is a contradiction between `edge_cond` and `conds`
        self.solver.push()
        for new_cond in new_conds:
            self.solver.add(os_z3wrapper.convert(self.thy, new_cond, self.convert_ctxt))
        for constraint in self.convert_ctxt.constraints:
            self.solver.add(constraint)
        res = self.solver.check()
        self.solver.pop()
        if str(res) == "unsat":
            if verbose:
                print(f"Condition check failed")
            return

        if verbose:
            print(f"Propagate {inst} to target {target}")
            print(f"  cur_conds = {', '.join(str(cond) for cond in cur_conds)}")
            print(f"  edge_conds = {', '.join(str(cond) for cond in get_new_conds(inst, var, edge_conds))}")

        # After checking these two conditions, we decide that the given
        # inst is possibly new and should be added
        if target not in self.node_inst:
            self.node_inst[target] = list()
        self.node_inst[target].append(new_ct)
        self.to_visit.put((target, new_ct))

    def propagate_edge(self, edge: Edge, ct: ConditionalTerm):
        """Propagate instantiation ct from source to target."""
        if isinstance(edge.target, QuantifierNode):
            var = edge.target.var
        elif isinstance(edge.source, QuantifierNode):
            var = edge.source.var
        else:
            var = None
        new_inst = os_term.get_plus(ct.t, edge.weight)
        self.add_node_inst(edge.target, new_inst, max(edge.generation, ct.generation),
                           cur_conds=ct.conds, var=var, edge_conds=edge.conds)

    def propagate(self):
        """Perform propagation."""
        num_round = 0
        max_round = 1000
        while not self.to_visit.empty() and num_round < max_round:
            num_round += 1
            node, ct = self.to_visit.get()

            # Propagate regular edges
            for edge in self.get_all_edges(node):
                assert edge.source == node
                self.propagate_edge(edge, ct)
                
            # Propagate between seq nodes with same name and index size
            if isinstance(node, SeqNode):
                for node2 in self.seq_nodes():
                    t1, t2 = node.seq_t, node2.seq_t
                    t1_name, t1_idx = os_term.dest_atomic_term(t1)
                    t2_name, t2_idx = os_term.dest_atomic_term(t2)
                    if t1 != t2 and t1_name == t2_name and len(t1_idx) == len(t2_idx):
                        eq_conds = [os_term.eq(id1, id2) for id1, id2 in zip(t1_idx, t2_idx)]
                        self.add_node_inst(node2, ct.t, ct.generation, cur_conds=ct.conds, edge_conds=eq_conds)
            
            # Propagate between map nodes with same name and index size
            if isinstance(node, MapNode):
                for node2 in self.map_nodes():
                    t1, t2 = node.map_t, node2.map_t
                    t1_name, t1_idx = os_term.dest_atomic_term(t1)
                    t2_name, t2_idx = os_term.dest_atomic_term(t2)
                    if t1 != t2 and t1_name == t2_name and len(t1_idx) == len(t2_idx):
                        eq_conds = [os_term.eq(id1, id2) for id1, id2 in zip(t1_idx, t2_idx)]
                        self.add_node_inst(node2, ct.t, ct.generation, cur_conds=ct.conds, edge_conds=eq_conds)

            # Propagate seq patterns
            if isinstance(node, SeqNode):
                for edge in self.get_all_seq_patterns(node):
                    tyinst = dict()
                    tinst: dict[str, OSTerm] = dict()
                    if os_match.match(edge.weight, ct.t, tyinst, tinst):
                        assert len(tinst) == 1
                        for _, inst_t in tinst.items():
                            self.add_node_inst(edge.target, inst_t, max(edge.generation, ct.generation),
                                               cur_conds=ct.conds)

            # Propagate map patterns
            if isinstance(node, MapNode):
                for edge in self.get_all_map_patterns(node):
                    tyinst = dict()
                    tinst: dict[str, OSTerm] = dict()
                    if os_match.match(edge.weight, ct.t, tyinst, tinst):
                        assert len(tinst) == 1
                        for _, inst_t in tinst.items():
                            self.add_node_inst(edge.target, inst_t, max(edge.generation, ct.generation),
                                               cur_conds=ct.conds)                    

        if num_round == max_round:
            raise AssertionError("Maximum number of rounds reached")
    
    def quant_nodes(self) -> list[QuantifierNode]:
        return list(node for node in self.get_all_nodes()
                    if isinstance(node, QuantifierNode))

    def seq_nodes(self) -> list[SeqNode]:
        return list(node for node in self.get_all_nodes()
                    if isinstance(node, SeqNode))

    def map_nodes(self) -> list[MapNode]:
        return list(node for node in self.get_all_nodes()
                    if isinstance(node, MapNode))

    def get_new_insts(self) -> dict[QuantifierNode, list[ConditionalTerm]]:
        res: dict[QuantifierNode, list[ConditionalTerm]] = dict()
        for node in self.node_inst:
            if isinstance(node, QuantifierNode):
                res[node] = list(self.node_inst[node])
        return res

    def __str__(self):
        res = []
        # res.append("- Basic conditions:")
        # for basic_cond in self.basic_conds:
        #     res.append("\n" + str(basic_cond))
        res.append("\n- Nodes:\n")
        res.append(", ".join(str(node) for node in self.nodes))
        res.append("\n- Edges:")
        for _, edges in self.edges.items():
            for edge in edges:
                res.append("\n" + str(edge))
        res.append("\n- Index inst:")
        for node, insts in self.index_inst.items():
            for inst in insts:
                res.append("\n" + f"{node}: {inst}")
        res.append("\n- Seq patterns:")
        for _, edges in self.seq_patterns.items():
            for edge in edges:
                res.append("\n" + str(edge))
        res.append("\n- Map patterns:")
        for _, edges in self.map_patterns.items():
            for edge in edges:
                res.append("\n" + str(edge))
        return ''.join(res)

    def print_instantiation(self):
        """Print instantiation information."""
        print("# Instantiation:")
        print("- Quantifier nodes:")
        for quant_node in self.quant_nodes():
            if quant_node in self.node_inst:
                print(str(quant_node) + ": " + ", ".join(
                    str(ct.t) for ct in self.node_inst[quant_node]))
                # for ct in self.node_inst[quant_node]:
                #     print(ct.t, ":", ", ".join(str(cond) for cond in ct.conds))
        print("- Sequence nodes:")
        for seq_node in self.seq_nodes():
            if seq_node in self.node_inst:
                print(str(seq_node) + ": " + ", ".join(
                    str(ct.t) for ct in self.node_inst[seq_node]))
        print("- Map nodes:")
        for map_node in self.map_nodes():
            if map_node in self.node_inst:
                print(str(map_node) + ": " + ", ".join(
                    str(ct.t) for ct in self.node_inst[map_node]))
        print()
