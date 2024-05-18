"""
Definition of structures
"""


from typing import Dict, Iterable, List, Set, Tuple, TypeGuard

class OSType:
    """Base class of types used in OS verification."""
    def subst(self, tyinst: Dict[str, "OSType"]) -> "OSType":
        """Substitute using the given instantiation of type variables.
        
        Both usual type variables (not starting with '?') and schematic
        type variables (starting with '?') may be substituted. In the
        case of schematic type variables, the keys in tyinst must start
        with '?'.

        Parameters
        ----------
        tyinst : Dict[str, OSType]
            instantiations for type variables.

        Returns
        -------
        OSType
            result after substitution of type variables.

        """
        raise NotImplementedError
    
    def match(self, other: "OSType", tyinst: Dict[str, "OSType"]) -> bool:
        """Match the current type with given type, update tyinst.

        Only schematic type variables may be matched. If matching on ordinary
        type variables are desired, first call `make_schematic` to convert
        them to schematic type variables.

        Parameters
        ----------
        other : OSType
            concrete type to be matched
        tyinst : Dict[str, OSType]
            instantiation of schematic type variables, updated during matching

        Returns
        -------
        bool
            whether the matching is successful.
        
        """
        raise NotImplementedError
    
    def get_vars_inplace(self, vars: List[str]):
        """Add set of type variables into vars.
        
        Override this function to implement for new subclasses of OSType.
        
        """
        raise NotImplementedError
    
    def get_vars(self) -> Tuple[str]:
        """Obtain the set of type variables."""
        vars = list()
        self.get_vars_inplace(vars)
        return tuple(vars)
    
    def make_schematic(self, vars: Iterable[str]) -> "OSType":
        """Change the given type variables into schematic type variables.
        
        In more detail, for each type variable `a` in `vars`, substitute it
        for the schematic type variable `?a`. This is done using the subst
        function.
        
        """
        tyinst = dict((var, OSBoundType('?' + var)) for var in vars)
        return self.subst(tyinst)


prim_types: List[str] = [
    "bool", "int", "int8u", "int16u", "int32u"
]

class OSPrimType(OSType):
    """Primitive types. Name must be one of prim_types."""
    def __init__(self, name: str):
        assert name in prim_types, "Unknown primitive type: %s" % name
        self.name = name

    def __eq__(self, other):
        return isinstance(other, OSPrimType) and self.name == other.name

    def __str__(self):
        return self.name
    
    def __repr__(self):
        return "OSPrimType(%s)" % self.name
    
    def __hash__(self):
        return hash(("OSPrimType", self.name))
    
    def subst(self, tyinst: Dict[str, OSType]) -> OSType:
        return self
    
    def match(self, other: OSType, tyinst: Dict[str, OSType]) -> bool:
        return self == other
    
    def get_vars_inplace(self, vars: List[str]):
        pass

class OSArrayType(OSType):
    """Array types"""
    def __init__(self, base_type: OSType):
        self.base_type = base_type

    def __eq__(self, other):
        return isinstance(other, OSArrayType) and self.base_type == other.base_type
    
    def __str__(self):
        return str(self.base_type) + "[]"
    
    def __repr__(self):
        return "OSArrayType(%s)" % repr(self.base_type)

    def __hash__(self):
        return hash(("OSArrayType", self.base_type))

    def subst(self, tyinst: Dict[str, OSType]) -> OSType:
        return OSArrayType(self.base_type.subst(tyinst))

    def match(self, other: OSType, tyinst: Dict[str, OSType]) -> bool:
        if not isinstance(other, OSArrayType):
            return False
        return self.base_type.match(other.base_type, tyinst)

    def get_vars_inplace(self, vars: List[str]):
        self.base_type.get_vars_inplace(vars)

class OSStructType(OSType):
    """Structure types."""
    def __init__(self, name: str):
        self.name = name

    def __eq__(self, other):
        return isinstance(other, OSStructType) and self.name == other.name

    def __str__(self):
        return self.name
    
    def __repr__(self):
        return "OSStructType(%s)" % self.name
    
    def __hash__(self):
        return hash(("OSStructType", self.name))

    def subst(self, tyinst: Dict[str, OSType]) -> OSType:
        return self

    def match(self, other: OSType, tyinst: Dict[str, OSType]) -> bool:
        return self == other

    def get_vars_inplace(self, vars: List[str]):
        pass

class OSHLevelType(OSType):
    """Defined types.
    
    This is used for types declared using typedef and datatypes.

    """
    def __init__(self, name: str, *params: OSType):
        self.name = name
        self.params = tuple(params)
        assert all(isinstance(param, OSType) for param in self.params), \
            "OSHLevelType: each parameter must be OSType"

    def __eq__(self, other):
        return isinstance(other, OSHLevelType) and self.name == other.name and \
            self.params == other.params

    def __str__(self):
        if len(self.params) == 0:
            return self.name
        else:
            return "%s<%s>" % (self.name, ", ".join(str(param) for param in self.params))
        
    def __repr__(self):
        if self.params:
            return "OSHLevelType(%s, %s)" % (self.name, ", ".join(repr(ty) for ty in self.params))
        else:
            return "OSHLevelType(%s)" % self.name
    
    def __hash__(self):
        return hash(("OSHLevelType", self.name, self.params))

    def subst(self, tyinst: Dict[str, OSType]) -> OSType:
        return OSHLevelType(self.name, *(param.subst(tyinst) for param in self.params))
    
    def match(self, other: OSType, tyinst: Dict[str, OSType]) -> bool:
        if not isinstance(other, OSHLevelType):
            return False
        if self.name != other.name:
            return False
        for i in range(len(self.params)):
            if not self.params[i].match(other.params[i], tyinst):
                return False
        return True

    def get_vars_inplace(self, vars: List[str]):
        for param in self.params:
            param.get_vars_inplace(vars)

class OSBoundType(OSType):
    """Bound type variable in datatype definitions."""
    def __init__(self, name: str):
        self.name = name
    
    def __eq__(self, other):
        return isinstance(other, OSBoundType) and self.name == other.name
    
    def __str__(self):
        return self.name
    
    def __repr__(self):
        return "OSBoundType(%s)" % self.name

    def __hash__(self):
        return hash(("OSBoundType", self.name))

    def subst(self, tyinst: Dict[str, OSType]) -> OSType:
        if self.name in tyinst:
            return tyinst[self.name]
        else:
            return self

    def match(self, other: OSType, tyinst: Dict[str, OSType]) -> bool:
        # Note matching is performed only for schematic type variables
        if not self.name.startswith('?'):
            return self == other
        elif self.name in tyinst:
            return tyinst[self.name] == other
        else:
            tyinst[self.name] = other
            return True

    def get_vars_inplace(self, vars: List[str]):
        if self.name not in vars:
            vars.append(self.name)

class OSFunctionType(OSType):
    """Function types"""
    def __init__(self, *types: OSType):
        self.arg_types = tuple(types[:-1])
        self.ret_type = types[-1]
        assert len(self.arg_types) > 0, "OSFunctionType: must have at least one argument"
        assert all(isinstance(type, OSType) for type in self.arg_types), \
            "OSFunctionType: arguments must be OSType"
        assert isinstance(self.ret_type, OSType), \
            "OSFunctionType: arguments must be OSType"

    def __eq__(self, other):
        return isinstance(other, OSFunctionType) and self.arg_types == other.arg_types and \
            self.ret_type == other.ret_type

    def __str__(self):
        return "%s -> %s" % (' -> '.join(str(arg_type) for arg_type in self.arg_types), self.ret_type)

    def __repr__(self):
        return "OSFunctionType(%s)" % ", ".join(repr(ty) for ty in self.arg_types + (self.ret_type,))

    def __hash__(self):
        return hash(("OSFunctionType", self.arg_types, self.ret_type))

    def subst(self, tyinst: Dict[str, OSType]) -> OSType:
        return OSFunctionType(*(arg_type.subst(tyinst) for arg_type in self.arg_types + (self.ret_type.subst(tyinst),)))

    def match(self, other: OSType, tyinst: Dict[str, OSType]) -> bool:
        if not isinstance(other, OSFunctionType):
            return False
        if len(self.arg_types) != len(other.arg_types):
            return False
        for i in range(len(self.arg_types)):
            if not self.arg_types[i].match(other.arg_types[i], tyinst):
                return False
        return self.ret_type.match(other.ret_type, tyinst)

    def get_vars_inplace(self, vars: List[str]):
        for arg_type in self.arg_types:
            arg_type.get_vars_inplace(vars)
        self.ret_type.get_vars_inplace(vars)

Bool: OSPrimType = OSPrimType("bool")
Nat: OSStructType = OSHLevelType("nat")
Int: OSPrimType = OSPrimType("int")
Int8U: OSPrimType = OSPrimType("int8u")
Int16U: OSPrimType = OSPrimType("int16u")
Int32U: OSPrimType = OSPrimType("int32u")
BvMap: Dict[int, OSPrimType] = {8: Int8U, 16: Int16U, 32: Int32U}

def MapType(K: OSType, V: OSType) -> OSType:
    return OSHLevelType("Map", K, V)

def isMapType(ty: OSType) -> TypeGuard[OSHLevelType]:
    return isinstance(ty, OSHLevelType) and ty.name == "Map"

def destMapType(ty: OSType) -> Tuple[OSType, OSType]:
    if not isinstance(ty, OSHLevelType) or ty.name != "Map":
        raise AssertionError("destMap")
    return ty.params[0], ty.params[1]

def isListType(ty: OSType) -> TypeGuard[OSHLevelType]:
    return isinstance(ty, OSHLevelType) and ty.name == "List"

def is_bv_type(type: OSType) -> bool:
    """Return whether the given type is a bitvector type."""
    return type == Int8U or type == Int16U or type == Int32U

def get_bv_type(size: int) -> OSType:
    """Return the bit-vector type according to its size."""
    if size in BvMap:
        return BvMap[size]
    else:
        raise AssertionError("get_bv_type: unknown size %s" % size)
    
def is_num_type(type: OSType) -> bool:
    """Return whether the given type is a numeric type."""
    return is_bv_type or type == Nat or type == Int

class StructField:
    """Each field in the structure consists of field name and
    field type.
    
    """
    def __init__(self, type: OSType, field_name: str):
        self.type = type
        self.field_name = field_name

    def __str__(self):
        return str(self.type) + " " + self.field_name

class Struct:
    """A structure maintains a list of structure fields.
    
    Attributes
    ----------
    struct_name : str
        name of the structure
    fields : Tuple[StructField]
        list of fields
    field_map : Dict[str, OSType]
        mapping from field name to their type. Note this should not be used
        to obtain types of actual terms, as they need to be instantiated.
        Use get_field_type function instead.

    """
    def __init__(self, struct_name: str, fields: Iterable[StructField]):
        self.struct_name = struct_name
        self.fields = tuple(fields)

        # Mapping from field name to field type
        self.field_map: Dict[str, OSType] = dict()
        for field in self.fields:
            if field.field_name in self.field_map:
                raise AssertionError("Struct: field %s already appeared" % field.field_name)
            self.field_map[field.field_name] = field.type

    def __str__(self):
        res = "struct %s {\n" % self.struct_name
        res += ";\n".join("  " + str(field) for field in self.fields)
        res += "\n}"
        return res

class ConstDef:
    """Definition of a constant."""
    def __init__(self, const_name: str, val = None):
        self.const_name = const_name
        self.val = val
    
    def __str__(self):
        return self.const_name + " = " + str(self.val)

class ConstDefList:
    """List of constant definitions."""
    def __init__(self, const_defs: Iterable[ConstDef]):
        self.const_defs = const_defs

    def __str__(self):
        res = "consts {\n"
        res += ";\n".join("  " + str(const_def) for const_def in self.const_defs)
        res += "\n}"
        return res

class TypeDef:
    """Type definition."""
    def __init__(self, type_name: str, type: OSType):
        self.type_name = type_name
        self.type = type

    def __str__(self):
        return "typedef %s = %s" % (self.type_name, self.type)
    
class AxiomDef:
    """Axiomatic function definition.
    
    Attributes
    ----------
    func_name : str
        name of the function
    type_params : Tuple[str]
        ordered list of type parameters
    type : OSType
        type of the function

    """
    def __init__(self, func_name: str, type_params: Iterable[str], type: OSType):
        self.func_name = func_name
        self.type_params = tuple(type_params)
        self.type = type

    def __str__(self):
        return "axiomdef %s" % self.func_name

class AxiomType:
    """Axiomatic type definition.

    Attributes
    ----------
    name : str
        name of the axiomatic type
    params : Tuple[str]
        list of parameters of the axiomatic type.

    """
    def __init__(self, name: str, params: Tuple[str]):
        self.name = name
        self.params = params
    
    def __str__(self):
        res = "axiomtype %s" % self.name
        if self.params:
            res += "<%s>" % ", ".join(self.params)
        return res

class DatatypeBranch:
    """Branch of a datatype definition.
    
    Attributes
    ----------
    constr_name : str
        name of the constructor of the branch
    params : Tuple[Tuple[str, OSType]]
        list of parameters of the constructor, in name-type pairs.

    """
    def __init__(self, constr_name: str, *params: Tuple[str, OSType]):
        self.constr_name = constr_name
        self.params = tuple(params)

    def __str__(self):
        if len(self.params) == 0:
            return self.constr_name
        else:
            return "%s(%s)" % (self.constr_name, ", ".join(name for name, _ in self.params))

class Datatype:
    """Datatype definition.
    
    Attributes
    ----------
    name : str
        name of the datatype
    params : Tuple[str]
        list of parameters to the datatype. These can be used as bound types
        in the types of fields in various branches.
    branches : Tuple[DatatypeBranch]
        list of branches of the datatype.
    field_map : Dict[str, OSType]
        mapping from field names to their type. Note this should NOT be used to
        obtain types of concrete terms, as they need to be instantiated. Use
        get_field_map function instead.
    branch_map : Dict[str, DatatypeBranch]
        mapping from branch names to corresponding branches.

    """
    def __init__(self, name: str, params: Iterable[str], *branches: DatatypeBranch):
        self.name = name
        self.params = tuple(params)
        self.branches = tuple(branches)
        if len(branches) == 0:
            raise AssertionError("Datatype: must have at least one branch")
        
        # Mapping from field name to field type
        self.field_map: Dict[str, OSType] = dict()
        for branch in self.branches:
            for param_name, param_type in branch.params:
                if param_name in self.field_map:
                    if self.field_map[param_name] != param_type:
                        raise AssertionError("Datatype: field %s with different types")
                else:
                    self.field_map[param_name] = param_type

        # Mapping from branch name to branches
        self.branch_map: Dict[str, DatatypeBranch] = dict()
        for branch in self.branches:
            self.branch_map[branch.constr_name] = branch

    def __str__(self):
        if len(self.params) == 0:
            res = "datatype %s =\n" % self.name
        else:
            res = "datatype %s<%s> =\n" % (self.name, ", ".join(str(param) for param in self.params))
        res += "    %s" % self.branches[0]
        for branch in self.branches[1:]:
            res += "\n  | %s" % branch
        return res

    def get_branch_id(self, constr_name: str) -> int:
        """Obtain id of the branch with given constructor name."""
        for i, branch in enumerate(self.branches):
            if branch.constr_name == constr_name:
                return i
        raise AssertionError("get_branch_id: branch %s not found" % constr_name)

    def get_field_id(self, constr_name: str, field: str) -> int:
        """Obtain id of the field with the given constructor name."""
        branch_id = self.get_branch_id(constr_name)
        for i, (param_name, _) in enumerate(self.branches[branch_id].params):
            if param_name == field:
                return i
        raise AssertionError("get_field_id: field %s not found in branch %s" % (field, constr_name))
