"""
Definitions in separation logic.
"""

from typing import Iterable, TypeGuard

from osverify.os_term import OSTerm
from osverify import os_struct
from osverify import os_term

class SepAssertion:
    """Base class for separation logic assertions."""
    def subst(self, inst: dict[str, OSTerm]) -> "SepAssertion":
        raise NotImplementedError


class SepFun(SepAssertion):
    """Atomic separation logic assertion given by function."""
    def __init__(self, func_name: str, *args: OSTerm):
        self.func_name = func_name
        self.args = tuple(args)

    def __str__(self):
        return "%s(%s)" % (self.func_name, ', '.join(str(arg) for arg in self.args))

    def __repr__(self):
        return "SepFun(%s, %s)" % (self.func_name, ', '.join(repr(arg) for arg in self.args))

    def __eq__(self, other):
        return isinstance(other, SepFun) and self.func_name == other.func_name and \
            self.args == other.args
    
    def subst(self, inst: dict[str, OSTerm]) -> SepAssertion:
        return SepFun(self.func_name, *(arg.subst(inst) for arg in self.args))


class SepConj(SepAssertion):
    """Conjunction of separation logic assertions."""
    def __init__(self, *parts: SepAssertion):
        self.parts = tuple(parts)

    def __str__(self):
        return '; '.join(str(part) for part in self.parts)

    def __repr__(self):
        return "SepConj(%s)" % (', '.join(repr(part) for part in self.parts))

    def __eq__(self, other):
        return isinstance(other, SepConj) and self.parts == other.parts

    def subst(self, inst: dict[str, OSTerm]) -> SepAssertion:
        return SepConj(*(part.subst(inst) for part in self.parts))


"""
Some special assertions.
"""
def sll(p: OSTerm, lst: OSTerm) -> SepFun:
    return SepFun("sll", p, lst)

def is_sll(asrt: SepAssertion) -> TypeGuard[SepFun]:
    return isinstance(asrt, SepFun) and asrt.func_name == "sll"


class Entails:
    """Entailment between two separation logic assertions."""
    def __init__(self, left: SepConj, right: SepConj, *,
                 assums: Iterable[OSTerm], goals: Iterable[OSTerm]):
        self.left = left
        self.right = right
        self.assums = tuple(assums)
        self.goals = tuple(goals)

    def __str__(self):
        res = "[%s]\n" % ', '.join(str(assum) for assum in self.assums)
        res += "%s\n" % self.left
        res += "|--\n"
        res += "%s\n" % self.right
        res += "[%s]\n" % ', '.join(str(goal) for goal in self.goals)
        return res

    def __repr__(self):
        return "Entails(%s, %s, %s, %s)" % (
            repr(self.left), repr(self.right), repr(self.assums), repr(self.goals))
    
    def __eq__(self, other):
        return isinstance(other, Entails) and self.assums == other.assums and \
            self.goals == other.goals and self.left == other.left and \
            self.right == other.right


class EntailsRule:
    """Base class of rules for transforming entailments."""
    def eval(self, entail: Entails) -> Entails:
        raise NotImplementedError


class EntailsRewriteRule(EntailsRule):
    """Apply rewriting rules.
    
    Find the first equality in the assumptions of the form x == t,
    where x is a variable, then use the equality to rewrite the other
    parts of the entailment, at the same time removing the equality
    from the assumptions.

    """
    def eval(self, entail: Entails) -> Entails:
        for i, assum in enumerate(entail.assums):
            if os_term.is_eq(assum) and isinstance(assum.args[0], os_term.OSVar):
                inst = {assum.args[0].name: assum.args[1]}
                new_assums = entail.assums[:i] + tuple(assum.subst(inst) for assum in entail.assums[i+1:])
                return Entails(
                    entail.left.subst(inst),
                    entail.right.subst(inst),
                    assums=new_assums,
                    goals=[goal.subst(inst) for goal in entail.goals]
                )
        return entail


class EntailsEmptyRule(EntailsRule):
    """Apply the rule sll(0, ls) --> ls == [].

    On the left side of entailment, find component of the form sll(0, ls),
    remove that component and add assumption ls == [].

    """
    def eval(self, entail: Entails) -> Entails:
        for i, part in enumerate(entail.left.parts):
            if is_sll(part) and part.args[0] == os_term.OSNumber(0, type=os_struct.Int32U):
                return Entails(
                    SepConj(*(entail.left.parts[:i] + entail.left.parts[i+1:])),
                    entail.right,
                    assums=entail.assums + (os_term.eq(part.args[1],
                                                       os_term.SeqLiteral([], type=part.args[1].type)),),
                    goals=entail.goals
                )
        return entail


class EntailsCancelRule(EntailsRule):
    """Cancel parts of the same type on both sides.
    
    """
    def eval(self, entail: Entails) -> Entails:
        for i, part in enumerate(entail.left.parts):
            for j, part2 in enumerate(entail.right.parts):
                if is_sll(part) and is_sll(part2) and part.args[0] == part2.args[0]:
                    return Entails(
                        SepConj(*(entail.left.parts[:i] + entail.left.parts[i+1:])),
                        SepConj(*(entail.right.parts[:j] + entail.right.parts[j+1:])),
                        assums=entail.assums,
                        goals=entail.goals + (os_term.eq(part.args[1], part2.args[1]),)
                    )
        return entail


rules: list[EntailsRule] = [
    EntailsRewriteRule(),
    EntailsEmptyRule(),
    EntailsCancelRule()
]

def reduceEntail(entail: Entails) -> Entails:
    while True:
        cur_entail = entail
        for rule in rules:
            entail = rule.eval(entail)
        if cur_entail == entail:
            break
    return entail
