"""
This file contains various utility functions.
"""

from typing import Set


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

def variant_names(names: Set[str], prefix: str) -> str:
    """Obtain a variant of prefix that is not in the set names.
    
    Parameters
    ----------
    names : Set[str]
        Names to avoid, usually the set of existing variables.
    prefix : str
        Suggested name, the returned name will always use this as prefix.
    """
    if prefix not in names:
        return prefix
    i = 0
    while True:
        if prefix + str(i) not in names:
            return prefix + str(i)
        i += 1
