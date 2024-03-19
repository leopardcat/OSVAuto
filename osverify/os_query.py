"""Queries in OS verification"""

from typing import Dict, Iterable

from osverify.os_struct import OSType
from osverify import os_term
from osverify.os_term import OSTerm
from osverify.os_util import indent


class Assumes:
    """Declare assumption of a query.
    
    Attributes
    ----------
    prop : OSTerm
        proposition of the assumption.
    name: str
        optional name of the assumption. This can be referred to in tactics.
        Assumptions without a name is indicated by the empty string.
    is_trigger : bool
        whether this assumption serves as a trigger when applying this theorem.

    """
    def __init__(self, prop: OSTerm, *,
                 name: str = "",
                 is_trigger: bool = False):
        prop.assert_type_checked()
        self.prop = prop
        self.name = name
        self.is_trigger = is_trigger

    def __str__(self):
        res = "assumes "
        if self.name:
            res += "%s: " % self.name
        if self.is_trigger:
            res += "[trigger] "
        res += str(self.prop)
        return res

    def __repr__(self):
        return "Assumes(%s)" % repr(self.prop)
    
    def __eq__(self, other):
        return isinstance(other, Assumes) and self.prop == other.prop

class Shows:
    """Declare conclusion of a query.
    
    Attributes
    ----------
    prop : OSTerm
        proposition of the conclusion.
    proof : Tactic
        tactic for proving this conclusion.
    is_trigger : bool
        whether this conclusion serves as a trigger when applying this theorem.

    """
    def __init__(self, prop: OSTerm, proof, *, is_trigger: bool = False):
        prop.assert_type_checked()
        self.prop = prop
        self.proof = proof
        self.is_trigger = is_trigger

    def __str__(self):
        res = "shows "
        if self.is_trigger:
            res += "[trigger] "
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

class Model:
    """Model as counterexample to a query."""
    def __init__(self):
        self.data: Dict[str, OSTerm] = dict()

    def __str__(self):
        res = ""
        for name, val in self.data.items():
            res += "%s := %s\n" % (name, val)
        return res


class Query:
    """Data structure representing a query.
    
    Attributes
    ----------
    query_name : str
        name of the query
    type_params : Tuple[str]
        list of type parameters
    fixes : Tuple[OSVar]
        list of fixed variables
    assumes : Tuple[Assumes]
        list of assumptions
    shows : Tuple[Shows]
        conclusion to be shown

    """
    def __init__(self, query_name: str,
                 type_params: Iterable[str], fixes: Iterable[os_term.OSVar],
                 assumes: Iterable[Assumes], shows: Iterable[Shows]):
        self.query_name = query_name
        self.type_params = tuple(type_params)
        self.fixes = tuple(fixes)
        self.assumes = tuple(assumes)
        self.shows = tuple(shows)

        # Dictionary from fixed variables to their types
        self.fixes_map: Dict[str, OSType] = dict()
        for fix in self.fixes:
            self.fixes_map[fix.name] = fix.type

    def __str__(self):
        res = "query %s {\n" % self.query_name
        res += ";\n".join(indent(str(decl)) for decl in self.type_params + self.fixes + self.assumes + self.shows)
        res += "\n}"
        return res
    
    def __repr__(self):
        return str(self)
        
    def __eq__(self, other):
        if not isinstance(other, Query):
            return False
        return self.query_name == other.query_name and self.type_params == other.type_params and \
            self.fixes == other.fixes and self.assumes == other.assumes and self.shows == other.shows
