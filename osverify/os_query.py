"""Queries in OS verification"""

from typing import Optional, Iterable, Union

from osverify.os_struct import OSType
from osverify import os_term
from osverify.os_term import OSTerm
from osverify.os_util import indent, short_form


# Global counter for generating unique names for assumptions
assume_counter = 0

class Meta:
    """Meta-information maintained for each assumption, goal, or variable
    declaration.
    
    """
    def __init__(self, *, initial_form: Optional[OSTerm] = None,
                 parent: Optional["StateItem"] = None,
                 quant_inst: Iterable[tuple[str, OSTerm]] = tuple(),
                 new_var: Iterable[os_term.OSVar] = tuple(),
                 contra: bool = False,
                 is_trigger: bool = False):
        # (ProofState) the initial form of an assumption or goal, which is
        # modified during splitting and instantiation, but not during usual
        # simplifications.
        self.initial_form = initial_form

        # (ProofState) parent of an assumption or goal. During splitting and
        # instantiation, the original assumption or goal is the parent.
        self.parent = parent

        # (ProofState) name of the assumption
        self.assume_name: str = ""

        # (ProofState) instantiation compared to previous parent
        self.quant_inst = tuple(quant_inst)

        # (ProofState) new variables created compared to previous parent
        self.new_var = tuple(new_var)

        # (ProofState) assumption created through proof by contradiction
        self.contra = contra

        # (Query) whether the assumption or goal is used as trigger.
        self.is_trigger = is_trigger

    def __repr__(self):
        return "Meta(initial_form=%s, parent=%s, contra=%s, is_trigger=%s)" % (
            repr(self.initial_form), repr(self.parent), repr(self.contra), repr(self.is_trigger)
        )
    
    def export(self) -> dict:
        """Export the meta information into json format."""
        return {
            "initial_form": str(self.initial_form),
            "quant_inst": list({"var": var, "t": str(t)} for var, t in self.quant_inst),
            "new_var": list(var.name for var in self.new_var),
            "contra": self.contra,
            "assume_name": self.assume_name
        }


class StateItem:
    """Base class for Assumes, Shows, and VarDecl.
    
    Attributes
    ----------
    meta: Meta
        meta information for the item

    """
    meta: Meta

    def get_chain(self) -> list[OSTerm]:
        """Given meta of the current assumption or goal, retrace the entire
        chain of meta information.
        
        """
        chain: list[OSTerm] = []
        if self.meta and self.meta.parent:
            chain = self.meta.parent.get_chain()
        if self.meta and self.meta.initial_form:
            chain.append(self.meta.initial_form)
        return chain

    def get_quant_insts(self) -> list[tuple[str, OSTerm]]:
        """Obtain the list of quantifier instantiations."""
        quant_insts: list[tuple[str, OSTerm]] = []

        if self.meta and self.meta.parent:
            quant_insts = self.meta.parent.get_quant_insts()
        if self.meta and self.meta.quant_inst:
            quant_insts.extend(self.meta.quant_inst)
        return quant_insts
    
    def get_new_vars(self) -> list[os_term.OSVar]:
        """Obtain the list of new variables created."""
        new_vars: list[os_term.OSVar] = []

        if self.meta and self.meta.parent:
            new_vars = self.meta.parent.get_new_vars()
        if self.meta and self.meta.new_var:
            new_vars.extend(self.meta.new_var)
        return new_vars

    def pprint_map(self) -> str:
        """Pretty-print the meta-information in text form."""
        res = ""
        chain = self.get_chain()
        if chain:
            res += "(" + " -> ".join(short_form(str(item)) for item in chain) + ") "
        quant_insts = self.get_quant_insts()
        if quant_insts:
            res += ", ".join("%s: %s" % (var, subst) for var, subst in quant_insts) + " "
        new_vars = self.get_new_vars()
        if new_vars:
            res += ", ".join("!%s: %s" % (var.name, var.type) for var in new_vars)
        return res
    
    def get_meta_list(self) -> list[Meta]:
        """Return list of meta-information."""
        res = self.meta.parent.get_meta_list() if self.meta and self.meta.parent else []
        if self.meta:
            res.append(self.meta)
        return res


class MetaTreeNode:
    def __init__(self, cur_meta: Meta):
        self.cur_meta: Meta = cur_meta
        self.childs: list[MetaTreeNode] = list()

    def export(self) -> dict:
        """Export the node to json format."""
        res = self.cur_meta.export()
        if self.childs:
            res["childs"] = []
            for child in self.childs:
                res["childs"].append(child.export())
        return res


def add_meta_list(node: MetaTreeNode, cur_list: list[Meta]):
    """The head of cur_list is assumed to equal to cur_meta at node."""
    assert len(cur_list) > 0
    if len(cur_list) == 1:
        return
    for child in node.childs:
        if child.cur_meta == cur_list[1]:
            add_meta_list(child, cur_list[1:])
            return
    # If not found, add new node
    node.childs.append(MetaTreeNode(cur_list[1]))
    add_meta_list(node.childs[-1], cur_list[1:])

def combine_meta_lists(meta_lists: list[list[Meta]]) -> list[MetaTreeNode]:
    res: list[MetaTreeNode] = list()
    for meta_list in meta_lists:
        if len(meta_list) > 0:
            found = False
            for node in res:
                if node.cur_meta == meta_list[0]:
                    add_meta_list(node, meta_list)
                    found = True
                    break
            # If not found, add new node
            if not found:
                res.append(MetaTreeNode(meta_list[0]))
                add_meta_list(res[-1], meta_list)
    return res

class Assumes(StateItem):
    """Declare assumption of a query.
    
    Attributes
    ----------
    prop : OSTerm
        proposition of the assumption.
    generation : int
        generation number
    conds : tuple[OSTerm]
        list of implicit conditions. These are used for condition checking
        during quantifier instantiation only.
    name : str
        optional name of the assumption. This can be referred to in tactics.
        Assumptions without a name is indicated by the empty string.
    is_trigger : bool
        whether this assumption serves as a trigger when applying this theorem.

    """
    def __init__(self, prop: OSTerm, *,
                 generation: int,
                 conds: Iterable[OSTerm],
                 name: str = "",
                 meta: Optional[Meta] = None):
        prop.assert_type_checked()
        self.prop = prop
        self.generation = generation
        self.conds = tuple(conds)
        if name == "":
            global assume_counter
            name = "_A%d" % assume_counter
            assume_counter += 1
        self.name = name
        self.meta = meta
        if self.meta:
            self.meta.assume_name = self.name

    def __str__(self):
        res = "assumes "
        if self.name:
            res += "%s: " % self.name
        res += str(self.prop)
        return res

    def __repr__(self):
        return "Assumes(%s)" % repr(self.prop)
    
    def __eq__(self, other):
        return isinstance(other, Assumes) and self.prop == other.prop

class Shows(StateItem):
    """Declare conclusion of a query.
    
    Attributes
    ----------
    prop : OSTerm
        proposition of the conclusion.
    proof : Optional[Tactic]
        tactic for proving this conclusion.
    is_trigger : bool
        whether this conclusion serves as a trigger when applying this theorem.

    """
    def __init__(self, prop: OSTerm, *, proof = None, meta: Optional[Meta] = None):
        prop.assert_type_checked()
        self.prop = prop
        self.proof = proof
        self.meta = meta

    def __str__(self):
        res = "shows "
        res += str(self.prop)
        if self.proof:
            res += "{\n"
            res += indent(str(self.proof)) + "\n"
            res += "}"
        return res

    def __repr__(self):
        return "Shows(%s)" % repr(self.prop)

    def __eq__(self, other):
        return isinstance(other, Shows) and self.prop == other.prop


class Query:
    """Data structure representing a query.
    
    Attributes
    ----------
    query_name : str
        name of the query
    type_params : tuple[str]
        list of type parameters
    fixes : tuple[OSVar]
        list of fixed variables
    assumes : tuple[Assumes]
        list of assumptions
    shows : tuple[Shows]
        conclusion to be shown
    is_axiom : bool (default to False)
        whether the query is intended to be an axiom (no proof needed)

    """
    def __init__(self, query_name: str,
                 type_params: Iterable[str], fixes: Iterable[os_term.OSVar],
                 assumes: Iterable[Assumes], shows: Iterable[Shows], *,
                 is_axiom: bool = False):
        self.query_name = query_name
        self.type_params = tuple(type_params)
        self.fixes = tuple(fixes)
        self.assumes = tuple(assumes)
        self.shows = tuple(shows)
        self.is_axiom = is_axiom

        # Dictionary from fixed variables to their types
        self.fixes_map: dict[str, OSType] = dict()
        for fix in self.fixes:
            self.fixes_map[fix.name] = fix.type

    def __str__(self):
        if self.is_axiom:
            res = "axiom %s {\n" % self.query_name
        else:
            res = "query %s {\n" % self.query_name
        for type_param in self.type_params:
            res += indent("type %s;" % type_param) + '\n'
        for var in self.fixes:
            res += indent("fixes %s: %s;" % (var.name, var.type)) + '\n'
        res += ";\n".join(indent(str(decl)) for decl in self.assumes + self.shows)
        res += "\n}"
        return res
    
    def __repr__(self):
        return str(self)
        
    def __eq__(self, other):
        if not isinstance(other, Query):
            return False
        return self.query_name == other.query_name and self.type_params == other.type_params and \
            self.fixes == other.fixes and self.assumes == other.assumes and self.shows == other.shows

    def get_var_context(self) -> os_term.VarContext:
        """Obtain the variable context of the query."""
        var_ctxt = os_term.VarContext(self.fixes)
        var_ctxt.type_params = list(self.type_params)
        return var_ctxt
