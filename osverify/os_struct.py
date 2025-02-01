"""
Definition of structures
"""


from typing import Iterable, TypeGuard

class OSType:
    """Base class of types used in OS verification."""
    def print_incr(self, res: list[str], indent: int):
        """Incrementally print the term."""
        raise NotImplementedError(f"print_incr on {type(self)}")

    def __str__(self):
        res: list[str] = []
        self.print_incr(res, 0)
        return ''.join(res)
        
    def subst(self, tyinst: dict[str, "OSType"]) -> "OSType":
        """Substitute using the given instantiation of type variables.
        
        Both usual type variables (not starting with '?') and schematic
        type variables (starting with '?') may be substituted. In the
        case of schematic type variables, the keys in tyinst must start
        with '?'.

        Parameters
        ----------
        tyinst : dict[str, OSType]
            instantiations for type variables.

        Returns
        -------
        OSType
            result after substitution of type variables.

        """
        raise NotImplementedError(f"subst on {type(self)}")
    
    def match(self, other: "OSType", tyinst: dict[str, "OSType"]) -> bool:
        """Match the current type with given type, update tyinst.

        Only schematic type variables may be matched. If matching on ordinary
        type variables are desired, first call `make_schematic` to convert
        them to schematic type variables.

        Parameters
        ----------
        other : OSType
            concrete type to be matched
        tyinst : dict[str, OSType]
            instantiation of schematic type variables, updated during matching

        Returns
        -------
        bool
            whether the matching is successful.
        
        """
        raise NotImplementedError(f"match on {type(self)}")
    
    def get_vars_inplace(self, vars: list[str]):
        """Add set of type variables into vars.
        
        Override this function to implement for new subclasses of OSType.
        
        """
        raise NotImplementedError(f"get_vars_inplace on {type(self)}")
    
    def get_vars(self) -> tuple[str]:
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


prim_types: list[str] = [
    "bool", "int",
    "int8u", "int16u", "int32u", "int64u",
    "int8", "int16", "int32", "int64"
]

class OSPrimType(OSType):
    """Primitive types. Name must be one of prim_types."""
    def __init__(self, name: str):
        assert name in prim_types, "Unknown primitive type: %s" % name
        self.name = name

    def __eq__(self, other):
        return isinstance(other, OSPrimType) and self.name == other.name

    def print_incr(self, res: list[str], indent: int):
        res.append(self.name)
    
    def __repr__(self):
        return "OSPrimType(%s)" % self.name
    
    def __hash__(self):
        return hash(("OSPrimType", self.name))
    
    def subst(self, tyinst: dict[str, OSType]) -> OSType:
        return self
    
    def match(self, other: OSType, tyinst: dict[str, OSType]) -> bool:
        return self == other
    
    def get_vars_inplace(self, vars: list[str]):
        pass

class OSStructType(OSType):
    """Structure types."""
    def __init__(self, name: str):
        self.name = name

    def __eq__(self, other):
        return isinstance(other, OSStructType) and self.name == other.name

    def print_incr(self, res: list[str], indent: int):
        res.append(self.name)
    
    def __repr__(self):
        return "OSStructType(%s)" % self.name
    
    def __hash__(self):
        return hash(("OSStructType", self.name))

    def subst(self, tyinst: dict[str, OSType]) -> OSType:
        return self

    def match(self, other: OSType, tyinst: dict[str, OSType]) -> bool:
        return self == other

    def get_vars_inplace(self, vars: list[str]):
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

    def print_incr(self, res: list[str], indent: int):
        res.append(self.name)
        if self.params:
            res.append("<")
            for i, param in enumerate(self.params):
                if i > 0:
                    res.append(", ")
                param.print_incr(res, indent)
            res.append(">")
        
    def __repr__(self):
        if self.params:
            return "OSHLevelType(%s, %s)" % (self.name, ", ".join(repr(ty) for ty in self.params))
        else:
            return "OSHLevelType(%s)" % self.name
    
    def __hash__(self):
        return hash(("OSHLevelType", self.name, self.params))

    def subst(self, tyinst: dict[str, OSType]) -> OSType:
        return OSHLevelType(self.name, *(param.subst(tyinst) for param in self.params))
    
    def match(self, other: OSType, tyinst: dict[str, OSType]) -> bool:
        if not isinstance(other, OSHLevelType):
            return False
        if self.name != other.name:
            return False
        for i in range(len(self.params)):
            if not self.params[i].match(other.params[i], tyinst):
                return False
        return True

    def get_vars_inplace(self, vars: list[str]):
        for param in self.params:
            param.get_vars_inplace(vars)

class OSBoundType(OSType):
    """Bound type variable in datatype definitions."""
    def __init__(self, name: str):
        self.name = name
    
    def __eq__(self, other):
        return isinstance(other, OSBoundType) and self.name == other.name
    
    def print_incr(self, res: list[str], indent: int):
        res.append(self.name)
    
    def __repr__(self):
        return "OSBoundType(%s)" % self.name

    def __hash__(self):
        return hash(("OSBoundType", self.name))

    def subst(self, tyinst: dict[str, OSType]) -> OSType:
        if self.name in tyinst:
            return tyinst[self.name]
        else:
            return self

    def match(self, other: OSType, tyinst: dict[str, OSType]) -> bool:
        # Note matching is performed only for schematic type variables
        if not self.name.startswith('?'):
            return self == other
        elif self.name in tyinst:
            return tyinst[self.name] == other
        else:
            tyinst[self.name] = other
            return True

    def get_vars_inplace(self, vars: list[str]):
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

    def print_incr(self, res: list[str], indent: str):
        for arg_type in self.arg_types:
            arg_type.print_incr(res, indent)
            res.append(" -> ")
        self.ret_type.print_incr(res, indent)

    def __repr__(self):
        return "OSFunctionType(%s)" % ", ".join(repr(ty) for ty in self.arg_types + (self.ret_type,))

    def __hash__(self):
        return hash(("OSFunctionType", self.arg_types, self.ret_type))

    def subst(self, tyinst: dict[str, OSType]) -> OSType:
        return OSFunctionType(*(arg_type.subst(tyinst) for arg_type in self.arg_types + (self.ret_type.subst(tyinst),)))

    def match(self, other: OSType, tyinst: dict[str, OSType]) -> bool:
        if not isinstance(other, OSFunctionType):
            return False
        if len(self.arg_types) != len(other.arg_types):
            return False
        for i in range(len(self.arg_types)):
            if not self.arg_types[i].match(other.arg_types[i], tyinst):
                return False
        return self.ret_type.match(other.ret_type, tyinst)

    def get_vars_inplace(self, vars: list[str]):
        for arg_type in self.arg_types:
            arg_type.get_vars_inplace(vars)
        self.ret_type.get_vars_inplace(vars)

Bool: OSPrimType = OSPrimType("bool")
Nat: OSStructType = OSHLevelType("nat")
Int: OSPrimType = OSPrimType("int")
Int8U: OSPrimType = OSPrimType("int8u")
Int16U: OSPrimType = OSPrimType("int16u")
Int32U: OSPrimType = OSPrimType("int32u")
Int64U: OSPrimType = OSPrimType("int64u")
Int8: OSPrimType = OSPrimType("int8")
Int16: OSPrimType = OSPrimType("int16")
Int32: OSPrimType = OSPrimType("int32")
Int64: OSPrimType = OSPrimType("int64")
BvMap: dict[int, OSPrimType] = {8: Int8U, 16: Int16U, 32: Int32U, 64: Int64U}
SignedBvMap: dict[int, OSPrimType] = {8: Int8, 16: Int16, 32: Int32, 64: Int64}

def MapType(K: OSType, V: OSType) -> OSType:
    return OSHLevelType("Map", K, V)

def is_map_type(ty: OSType) -> TypeGuard[OSHLevelType]:
    return isinstance(ty, OSHLevelType) and ty.name == "Map"

def dest_map_type(ty: OSType) -> tuple[OSType, OSType]:
    if not isinstance(ty, OSHLevelType) or ty.name != "Map":
        raise AssertionError("destMap")
    return ty.params[0], ty.params[1]

def SeqType(T: OSType) -> OSType:
    """Construct type Seq<T> from T."""
    return OSHLevelType("Seq", T)

def is_seq_type(T: OSType) -> TypeGuard[OSHLevelType]:
    """Test whether type has form Seq<T>."""
    return isinstance(T, OSHLevelType) and T.name == "Seq"

def is_bv_type(type: OSType) -> TypeGuard[OSPrimType]:
    """Return whether the given type is a bitvector type."""
    return type in (
        Int8U, Int16U, Int32U, Int64U,
        Int8, Int16, Int32, Int64
    )

def is_unsigned_bv_type(type: OSType) -> TypeGuard[OSPrimType]:
    """Return whether the given type is an unsigned bitvector type."""
    return type in (
        Int8U, Int16U, Int32U, Int64U
    )

def is_signed_bv_type(type: OSType) -> TypeGuard[OSPrimType]:
    """Return whether the given type is a signed bitvector type."""
    return type in (
        Int8, Int16, Int32, Int64
    )

def get_bv_type(size: int) -> OSPrimType:
    """Return the bit-vector type according to its size."""
    if size in BvMap:
        return BvMap[size]
    else:
        raise AssertionError("get_bv_type: unknown size %s" % size)

def get_signed_bv_type(size: int) -> OSPrimType:
    """Return the signed bit-vector type according to its size."""
    if size in SignedBvMap:
        return SignedBvMap[size]
    else:
        raise AssertionError("get_signed_bv_type: unknown size %s" % size)

def is_num_type(type: OSType) -> bool:
    """Return whether the given type is a numeric type."""
    return is_bv_type(type) or type == Nat or type == Int

class StructField:
    """Describes a single field in the structure.

    Possible annotations for a structure field are:
    - "binary", "octal", "hex": specifies how the field is printed.
     
    Attributes
    ----------
    type: OSType
        type of the field
    field_name: str
        name of the field
    annotations: tuple[str]
        list of annotations
    
    """
    def __init__(self, type: OSType, field_name: str, annotations: Iterable[str] = tuple()):
        self.type = type
        self.field_name = field_name
        self.annotations = tuple(annotations)

    def __str__(self):
        res = str(self.type) + " " + self.field_name
        if self.annotations:
            res += " [" + ", ".join(self.annotations) + "]"
        return res

class Struct:
    """A structure maintains a list of structure fields.
    
    Attributes
    ----------
    struct_name : str
        name of the structure
    fields : tuple[StructField]
        list of fields
    field_map : dict[str, OSType]
        mapping from field name to their type. Note this should not be used
        to obtain types of actual terms, as they need to be instantiated.
        Use get_field_type function instead.

    """
    def __init__(self, struct_name: str, fields: Iterable[StructField]):
        self.struct_name = struct_name
        self.fields = tuple(fields)

        # Mapping from field name to field type
        self.field_map: dict[str, OSType] = dict()
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
    type_params : tuple[str]
        ordered list of type parameters
    type : OSType
        type of the function

    """
    def __init__(self, func_name: str, type_params: Iterable[str], type: OSType):
        self.func_name = func_name
        self.type_params = tuple(type_params)
        self.type = type

    def __str__(self):
        ty_params = ""
        if len(self.type_params) > 0:
            ty_params = "<" + ', '.join(str(param) for param in self.type_params) + ">"
        return f"axiomdef {self.func_name}{ty_params}: {self.type}"

class AxiomType:
    """Axiomatic type definition.

    Attributes
    ----------
    name : str
        name of the axiomatic type
    params : tuple[str]
        list of parameters of the axiomatic type.

    """
    def __init__(self, name: str, params: tuple[str]):
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
    params : tuple[tuple[str, OSType]]
        list of parameters of the constructor, in name-type pairs.

    """
    def __init__(self, constr_name: str, *params: tuple[str, OSType]):
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
    params : tuple[str]
        list of parameters to the datatype. These can be used as bound types
        in the types of fields in various branches.
    branches : tuple[DatatypeBranch]
        list of branches of the datatype.
    field_map : dict[str, OSType]
        mapping from field names to their type. Note this should NOT be used to
        obtain types of concrete terms, as they need to be instantiated. Use
        get_field_map function instead.
    branch_map : dict[str, DatatypeBranch]
        mapping from branch names to corresponding branches.

    """
    def __init__(self, name: str, params: Iterable[str], *branches: DatatypeBranch):
        self.name = name
        self.params = tuple(params)
        self.branches = tuple(branches)
        if len(branches) == 0:
            raise AssertionError("Datatype: must have at least one branch")
        
        # Mapping from field name to field type
        self.field_map: dict[str, OSType] = dict()
        for branch in self.branches:
            for param_name, param_type in branch.params:
                if param_name in self.field_map:
                    if self.field_map[param_name] != param_type:
                        raise AssertionError("Datatype: field %s with different types")
                else:
                    self.field_map[param_name] = param_type

        # Mapping from branch name to branches
        self.branch_map: dict[str, DatatypeBranch] = dict()
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
