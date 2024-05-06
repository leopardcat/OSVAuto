"""
Definition of function
"""

from typing import Iterable, Tuple
from osverify import os_term
from osverify import os_struct
from osverify.os_util import indent

class OSFunction:
    def __init__(self, name: str, type_params: Iterable[str],
                 params: Iterable[os_term.OSVar],
                 ret_type: os_struct.OSType, body: os_term.OSTerm):
        self.name = name
        self.type_params = tuple(type_params)
        self.params = tuple(params)
        self.ret_type = ret_type
        self.body = body

    def __str__(self) -> str:
        res = "function %s" % self.name
        if self.type_params:
            res += "<" + ", ".join(self.type_params) + ">"
        res += "(" + ", ".join(str(param) for param in self.params) + ") -> "
        res += str(self.ret_type) + " {\n"
        res += indent(str(self.body))
        res += "\n}"
        return res
    
    def get_func_type(self) -> os_struct.OSType:
        """Return the function type for this definition."""
        if len(self.params) == 0:
            return self.ret_type
        else:
            arg_types = list()
            for param in self.params:
                arg_types.append(param.type)
            return os_struct.OSFunctionType(*(arg_types + [self.ret_type]))

    def is_recursive_func(self) -> bool:
        """Return whether the function definition is a recursive function.
        
        TODO: check for mutually recursive definitions.
        
        """
        return (self.name, self.get_func_type()) in self.body.get_funcs()
