"""Parser for OS verification"""

from lark import Lark, Transformer, v_args, exceptions, Token

from typing import Iterable, List, Set, Tuple, Optional, Union

from osverify import os_struct
from osverify import os_term
from osverify import os_query
from osverify import os_theory
from osverify import os_tactics
from osverify.os_theory import OSTheory, OSContext
from osverify.os_fixp import OSFunction
from osverify.os_struct import OSType
from osverify.os_term import OSTerm, OSOp
from osverify.os_tactics import Tactic

os_verify_grammar = r"""
    // Primitive types
    ?os_prim_type: "bool" -> bool_type
            | "int" -> int_type
            | "int8u" -> int8u_type
            | "int16u" -> int16u_type
            | "int32u" -> int32u_type

    // General types
    ?os_atom_type: "void" -> os_void_type
            | os_prim_type
            | os_atom_type "*" -> os_pointer_type
            | os_atom_type "[]" -> os_arr_type
            | CNAME -> os_hlevel_type
            | "?" CNAME -> os_sch_type
            | CNAME "<" os_type ("," os_type)* ">" -> os_hlevel_param_type
            | "(" os_type ")"

    ?os_type: (os_atom_type "->")+ os_atom_type -> os_fun_type
            | os_atom_type

    // Field of a structure
    ?os_field: os_type CNAME

    // Structure definition
    ?os_struct_def: "struct" CNAME "{" (os_field ";")* "}"

    // Constant definitions
    ?os_const_def: CNAME "=" INT

    ?os_consts: "consts" "{" (os_const_def ";")* "}"

    // Auxiliary for structure update
    ?field_update: CNAME ":=" os_term

    ?ori_struct: CNAME -> ori_struct_name
        | "[[" os_typed_term "]]" -> ori_struct_expr

    // Auxiliary for structure value
    ?struct_field: CNAME ":" os_term

    ?struct_name: CNAME -> struct_name

    // Auxiliary for let expression
    ?let_assign: CNAME "=" os_term

    // Patterns in case expression
    ?case_struct_field: CNAME ":" case_pat

    ?case_pat: CNAME -> case_pat_var
            | INT -> case_pat_number
            | CNAME "(" case_pat ("," case_pat)* ")" -> case_pat_constr
            | struct_name "{{" "}}" -> case_pat_struct_empty
            | struct_name "{{" case_struct_field ("," case_struct_field)* "}}" -> case_pat_struct

    ?case_branch: "case" case_pat ":" os_term -> case_branch
            | "default" ":" os_term -> default_branch

    // Local variable declaration
    ?os_localv: os_type CNAME

    ?os_params: os_localv ("," os_localv)* -> os_params

    ?os_atom: CNAME -> vname
            | "?" CNAME -> sch_vname
            | "?" -> unknown
            | os_atom "::" os_type -> atom_with_type
            | INT -> number
            | ori_struct "{" field_update ("," field_update)* "}" -> struct_update
            | struct_name "{{" struct_field ("," struct_field)* "}}" -> struct_val
            | CNAME "(" os_term ("," os_term)* ")" -> function_app
            | "[" "]" -> empty_list
            | "[" os_term ("," os_term)* "]" -> literal_list
            | "(" os_term ")"                                // Parenthesis
            | os_atom "[" os_term "]" -> array_index         // Array indexing
            | os_atom "[" os_term ":=" os_term "]" -> array_store  // Array store
            | os_atom "." CNAME -> member_get                // Structure field
            | "let" let_assign "in" os_term "end" -> let_in  // Let-in expression
            | "switch" "(" os_term ")" "{" (case_branch ";")* "}" -> switch_case
            | "if" "(" os_term ")" "{" os_term "}" "else" "{" os_term "}" -> ite
            | "forall" "(" os_params ")" "{" os_term "}" -> forall  // Forall expression
            | "exists" "(" os_params ")" "{" os_term "}" -> exists  // Exists expression
            | "forall" "(" os_localv "in" os_term ")" "{" os_term "}" -> forall_in
            | "exists" "(" os_localv "in" os_term ")" "{" os_term "}" -> exists_in

    ?negation: "!" negation -> bneg
            | "~" negation -> bvneg
            | "-" negation -> uminus
            | os_atom                               // priority 90

    ?times: times "*" negation -> times
            | times "/" negation -> divides
            | negation                              // priority 87

    ?plus: plus "+" times -> plus
            | plus "-" times -> minus
            | times                                 // priority 85

    ?bvshift: bvshift "<<" plus -> bvshiftl
            | bvshift ">>" plus -> bvshiftr
            | plus                                  // priority 80

    ?bvand: bvand "&" bvshift -> bvand
            | bvshift                               // priority 70

    ?bvxor: bvxor "^" bvand -> bvxor
            | bvand                                 // priority 65

    ?bvor: bvor "|" bvxor -> bvor
            | bvxor                                 // priority 60

    ?compare: compare "<" bvor -> less
            | compare "<=" bvor -> less_eq
            | compare ">" bvor -> greater
            | compare ">=" bvor -> greater_eq
            | compare "==" bvor -> eq
            | compare "!=" bvor -> not_eq
            | bvor                                  // priority 50
                        
    ?conj: compare "&&" conj -> conj
            | compare                               // priority 35

    ?disj: conj "||" disj -> disj
            | conj                                  // priority 30

    ?impl: disj "->" impl -> impl
            | disj

    ?os_term: impl

    ?os_typed_term: os_term -> os_typed_term
   
    // Declaration of functions
    ?os_axiom_func: "axiomfunc" function_name ":" os_type -> os_axiom_func

    ?function_name: CNAME -> function_name
            | CNAME "<" CNAME ("," CNAME)* ">" -> function_name_params

    ?os_function: "function" function_name "(" os_params ")" "->" os_type "{" os_term "}"

    ?os_predicate: "predicate" function_name "(" os_params ")" "{" os_term "}"

    // Tactics
    ?tactic_branch: "case" CNAME ":" tactic -> tactic_branch_case
            | "case" CNAME "(" CNAME ("," CNAME)* ")" ":" tactic -> tactic_branch_case_params
            | INT ":" tactic -> tactic_branch_case_index
            | "default" ":" tactic -> tactic_branch_default

    ?induction_param: CNAME -> induction_param_basic
            | CNAME "," "[" CNAME ("," CNAME)* "]" -> induction_param_arbitrary

    ?apply_param: CNAME -> apply_param_basic
            | CNAME "," "[" CNAME ("," CNAME)* "]" -> apply_param_facts

    ?thm_spec: CNAME -> thm_spec
            | CNAME "<" os_type ("," os_type)* ">" -> thm_spec_type

    ?tactic_atom: "skip" -> skip_tactic
            | "auto" ("(" thm_spec ("," thm_spec)* ")")? -> auto_tactic
            | "cases" "(" os_typed_term ")" "{" (tactic_branch ";")* "}" -> cases_tactic
            | "induction" "(" induction_param ")" "{" (tactic_branch ";")* "}" -> induction_tactic
            | "assumption" -> assumption_tactic
            | "simplify" -> simplify_tactic
            | "exists" "(" os_typed_term ("," os_typed_term)* ")" -> exists_tactic
            | "skolemize" "(" CNAME "," "[" os_localv ("," os_localv)* "]" ")" -> skolemize_tactic
            | "assert" "(" CNAME ":" os_typed_term ")" "{" tactic "}" -> assert_tactic
            | "change" "(" os_typed_term ")" "{" tactic "}" -> change_tactic
            | "split_conj" "(" CNAME "," "[" CNAME ("," CNAME)* "]" ")" -> split_conj_tactic
            | "match_show" "(" CNAME ")" -> match_show_tactic
            | "apply_theorem" "(" apply_param ")" -> apply_theorem_tactic

    ?tactic: tactic_atom
            | tactic_atom ";;" tactic -> then_tactic
            | tactic_atom "{" (tactic_branch ";")* "}" -> then_split_tactic

    // Query declarations
    ?type_param: "type" CNAME -> type_param

    ?fixes: "fixes" CNAME ":" os_type

    ?assumes: "assumes" os_typed_term -> assumes
            | "assumes" CNAME ":" os_typed_term -> assumes_named
            | "assumes" "[trigger]" os_typed_term -> assumes_trig
            | "assumes" CNAME "[trigger]" ":" os_typed_term -> assumes_named_trig

    ?shows: "shows" os_typed_term -> shows
            | "shows" "[trigger]" os_typed_term -> shows_trig
            | "shows" os_typed_term "proof" "{" tactic "}" -> shows_proof
            | "shows" "[trigger]" os_typed_term "proof" "{" tactic "}" -> shows_trig_proof

    ?query_decl: type_param | fixes | assumes | shows

    // Query definition
    ?os_query_def: "query" CNAME "{" query_decl (";" query_decl)* "}"

    // Type alias definition
    ?os_typedef: "typedef" CNAME "=" os_type ";"

    // Datatype definition
    ?datatype_branch: CNAME -> datatype_branch_single
            | CNAME "(" os_params ")" -> datatype_branch_param

    ?datatype_name: CNAME -> datatype_name
            | CNAME "<" CNAME ("," CNAME)* ">" -> datatype_name_params

    ?os_datatype: "datatype" datatype_name "=" datatype_branch ("|" datatype_branch)*
            | "axiomtype" datatype_name -> os_axiomtype

    ?os_attrib_decl: "add_attrib" CNAME "for" CNAME ("," CNAME)* -> os_add_attrib
            | "del_attrib" CNAME "for" CNAME ("," CNAME)* -> os_del_attrib

    ?os_imports: "imports" CNAME ("," CNAME)* -> os_imports

    ?os_theory_item: os_imports -> os_theory_item
            | os_struct_def -> os_theory_item
            | os_consts -> os_theory_item
            | os_function -> os_theory_item
            | os_predicate -> os_theory_item
            | os_query_def -> os_theory_item
            | os_typedef -> os_theory_item
            | os_datatype -> os_theory_item
            | os_axiom_func -> os_theory_item
            | os_attrib_decl -> os_theory_item

    ?os_theory_items: os_theory_item* -> os_theory_items

    // Proof state definition
    ?os_proof_state: "state" "{" query_decl (";" query_decl)* "}" -> os_proof_state

    // Context declaration
    ?os_context: "context" "{" query_decl (";" query_decl)* "}" -> os_context

    COMMENT: /\/\/.*/ | /\/\*+([\s\S]*?)\*\//

    %import common.CNAME
    %import common.INT
    %import common.DIGIT
    %import common.LETTER
    %import common.DECIMAL
    %import common.WS
    %import common.NUMBER

    %ignore WS
    %ignore COMMENT
"""

@v_args(inline=True)
class OSVerifyTransformer(Transformer):
    def __init__(self, thy: OSTheory, *,
                 ctxt: Optional[OSContext] = None,
                 visited: Set[str] = set(),
                 check_proof: Union[bool, str] = False,
                 verbose=False):
        self.thy = thy
        if ctxt is None:
            self.ctxt = OSContext(thy)
        else:
            self.ctxt = ctxt
        self.visited = visited
        self.check_proof = check_proof
        self.verbose = verbose

    def print_verbose(self, s: str):
        if self.verbose:
            print(s)

    def bool_type(self) -> OSType:
        return os_struct.OSPrimType("bool")
    
    def int_type(self) -> OSType:
        return os_struct.OSPrimType("int")

    def int8u_type(self) -> OSType:
        return os_struct.OSPrimType("int8u")
    
    def int16u_type(self) -> OSType:
        return os_struct.OSPrimType("int16u")

    def int32u_type(self) -> OSType:
        return os_struct.OSPrimType("int32u")
    
    def os_void_type(self) -> OSType:
        return os_struct.OSVoidType()
    
    def os_pointer_type(self, type: OSType) -> OSType:
        return os_struct.OSPointerType(type)
    
    def os_arr_type(self, type: OSType) -> OSType:
        return os_struct.OSArrayType(type)
    
    def os_hlevel_type(self, name: Token) -> OSType:
        name = str(name)
        if self.thy.is_defined_type(name):
            return os_struct.OSHLevelType(name)
        elif name in self.thy.structs:
            return os_struct.OSStructType(name)
        elif name == self.ctxt.datatype_decl:
            return os_struct.OSHLevelType(name)
        elif name in self.ctxt.type_params:
            return os_struct.OSBoundType(name)
        else:
            raise AssertionError("Type %s not found" % name)
    
    def os_hlevel_param_type(self, name: Token, *params: OSType) -> OSType:
        name = str(name)
        if self.thy.is_defined_type(name):
            return os_struct.OSHLevelType(name, *params)
        elif name == self.ctxt.datatype_decl:
            return os_struct.OSHLevelType(name, *params)
        elif name in self.thy.axiom_types:
            return os_struct.OSHLevelType(name, *params)
        else:
            raise AssertionError("Type %s not found" % name)
    
    def os_sch_type(self, name: Token) -> OSType:
        return os_struct.OSBoundType("?" + str(name))

    def os_fun_type(self, *tys: OSType) -> OSType:
        return os_struct.OSFunctionType(*tys)

    def os_field(self, type: OSType, field_name: Token) -> os_struct.StructField:
        return os_struct.StructField(os_theory.expand_type(self.thy, type), str(field_name))

    def os_struct_def(self, struct_name: Token, *fields) -> os_struct.Struct:
        return os_struct.Struct(str(struct_name), fields)

    def os_const_def(self, const_name: Token, val: Token) -> os_struct.ConstDef:
        return os_struct.ConstDef(str(const_name), int(val))

    def os_consts(self, *const_defs) -> os_struct.ConstDefList:
        return os_struct.ConstDefList(const_defs)

    def vname(self, name: Token) -> OSTerm:
        name = str(name)
        if name == 'true':
            return os_term.OSNumber(True)
        elif name == 'false':
            return os_term.OSNumber(False)
        elif name in self.thy.const_val:
            # Constant
            return os_term.OSConst(name)
        elif name in self.thy.constr_types:
            # Constructor
            return os_term.OSFun(name)
        elif name in self.ctxt.var_decls:
            # Declared variable
            return os_term.OSVar(name)
        elif name in self.ctxt.bound_vars:
            # Bound variable
            return os_term.OSVar(name)
        else:
            # Field of default structure
            ty = self.ctxt.lookup_field(name)
            if ty is None:
                raise AssertionError("Variable %s not found" % name)
            else:
                return os_term.OSVar(name, type=ty)
    
    def sch_vname(self, name: Token) -> OSTerm:
        return os_term.OSVar('?' + str(name))

    def unknown(self) -> OSTerm:
        return os_term.OSUnknown()

    def atom_with_type(self, expr: OSTerm, ty: OSType) -> OSTerm:
        expr.type = os_theory.expand_type(self.thy, ty)
        return expr

    def number(self, val: Token) -> OSTerm:
        return os_term.OSNumber(int(val))

    def field_update(self, field_name: Token, expr: OSTerm) -> OSTerm:
        field_name = str(field_name)
        # Check field with the given name exists
        if self.ctxt.lookup_field(field_name) is None:
            raise AssertionError("field %s is not found" % field_name)
        return os_term.FieldUpdate(field_name, expr)

    def ori_struct_name(self, name: Token) -> OSTerm:
        name = str(name)
        if name not in self.ctxt.var_decls:
            raise AssertionError("struct_update: variable %s not found" % name)
        var_type = self.ctxt.var_decls[name]
        if not isinstance(var_type, os_struct.OSStructType):
            raise AssertionError("struct_update: original term %s is not of structure type" % name)
        self.ctxt.default_struct.append(var_type.name)
        return os_term.OSVar(name)

    def ori_struct_expr(self, expr: OSTerm) -> OSTerm:
        # Set default structure when parsing an update
        ty = expr.type
        if not isinstance(ty, os_struct.OSStructType):
            raise AssertionError("struct_update: original term %s is not of structure type" % ty.name)
        self.ctxt.default_struct.append(ty.name)
        return expr
    
    def struct_update(self, ori_struct: OSTerm, *updates) -> OSTerm:
        # Clear default structure after parsing an update
        del self.ctxt.default_struct[-1]

        return os_term.OSStructUpdate(ori_struct, updates)
    
    def struct_field(self, field_name: Token, expr: OSTerm) -> Tuple[str, OSTerm]:
        field_name = str(field_name)
        # Check field with the given name exists
        if self.ctxt.lookup_field(field_name) is None:
            raise AssertionError("field %s is not found" % field_name)
        return field_name, expr

    def struct_name(self, name: Token) -> str:
        # Set default structure when parsing a structure value
        name = str(name)
        if name not in self.thy.structs:
            raise AssertionError("struct_val: structure %s not found" % name)
        self.ctxt.default_struct.append(name)
        return name

    def struct_val(self, name: str, *fields: Tuple[str, OSTerm]) -> OSTerm:
        # Clear default structure after parsing a value
        del self.ctxt.default_struct[-1]

        # Check all fields are filled
        struct = self.thy.structs[name]
        filled_fields = [field_name for field_name, _ in fields]
        for field in struct.field_map:
            if field not in filled_fields:
                raise AssertionError("struct_val: field %s does not have value" % field)
        return os_term.OSStructVal(name, fields)
    
    def function_app(self, func_name: Token, *args: OSTerm) -> OSTerm:
        """if function is an axiomatic function, find var type from var_decl"""
        return os_term.OSFun(str(func_name), *args)

    def empty_list(self) -> OSTerm:
        return os_term.OSFun("nil")

    def literal_list(self, *ts: OSTerm) -> OSTerm:
        res = os_term.OSFun("nil")
        for t in reversed(list(ts)):
            res = os_term.OSFun("cons", t, res)
        return res

    def array_index(self, arr: OSTerm, idx: OSTerm) -> OSTerm:
        return os_term.OSFun("nth", arr, idx)
    
    def array_store(self, arr: OSTerm, idx: OSTerm, t: OSTerm) -> OSTerm:
        return os_term.OSFun("Store", arr, idx, t)

    def member_get(self, expr: OSTerm, field_name: Token) -> OSTerm:
        return os_term.FieldGet(expr, str(field_name))

    def case_struct_field(self, field_name: Token, pat: OSTerm) -> Tuple[str, OSTerm]:
        field_name = str(field_name)
        # Check field with the given name exists
        if self.ctxt.lookup_field(field_name) is None:
            raise AssertionError("field %s is not found" % field_name)
        return field_name, pat

    def case_pat_var(self, name: Token) -> OSTerm:
        name = str(name)
        if name == "_":
            return os_term.OSWildcard()
        elif name == 'true':
            return os_term.OSNumber(True)
        elif name == 'false':
            return os_term.OSNumber(False)
        elif name in self.thy.constr_types:
            # Constructor
            return os_term.OSFun(name)
        else:
            # Bound variable
            if name in self.ctxt.bound_vars or name in self.ctxt.var_decls:
                raise AssertionError("case_pat_var: variable %s already defined" % name)
            self.ctxt.bound_vars.append(name)
            return os_term.OSVar(name)
    
    def case_pat_number(self, val: Token) -> OSTerm:
        return os_term.OSNumber(int(val))

    def case_pat_constr(self, name: Token, *args: OSTerm) -> OSTerm:
        name = str(name)
        if name not in self.thy.constr_datatype:
            raise AssertionError("case_pat_constr: constructor %s not defined" % name)
        return os_term.OSFun(name, *args)
    
    def case_pat_struct_empty(self, struct_name: str) -> OSTerm:
        return os_term.OSStructVal(struct_name, tuple())

    def case_pat_struct(self, struct_name: str, *vals: Tuple[str, OSTerm]) -> OSTerm:
        # Clear default structure after parsing a value
        del self.ctxt.default_struct[-1]

        return os_term.OSStructVal(struct_name, vals)

    def case_branch(self, pattern: OSTerm, expr: OSTerm) -> os_term.OSSwitchBranch:
        _, bound_vars = pattern.get_vars()
        for var in bound_vars:
            self.ctxt.bound_vars.remove(var.name)
        return os_term.OSSwitchBranchCase(pattern, expr)

    def default_branch(self, expr: os_term.OSTerm) -> os_term.OSSwitchBranch:
        return os_term.OSSwitchBranchDefault(expr)

    def switch_case(self, var_name: str, *branches: os_term.OSSwitchBranch) -> OSTerm:
        if len(branches) > 0 and isinstance(branches[0], os_term.OSSwitchBranchCase) and \
            isinstance(branches[0].pattern, os_term.OSStructVal):
            assert len(branches) == 1 or \
                (len(branches) == 2 and isinstance(branches[1], os_term.OSSwitchBranchDefault)), \
                "switch_case: if pattern is structure, there can be no other branches."
        return os_term.OSSwitch(var_name, branches)

    def ite(self, cond: OSTerm, if_branch: OSTerm, else_branch: OSTerm) -> OSTerm:
        return os_term.OSFun("ite", cond, if_branch, else_branch)

    def let_assign(self, var_name: Token, expr: OSTerm):
        var_name = str(var_name)
        if var_name in self.ctxt.var_decls or var_name in self.ctxt.bound_vars:
            raise AssertionError("let: variable %s already defined" % var_name)
        self.ctxt.bound_vars.append(var_name)
        return var_name, expr

    def let_in(self, let_assign, rhs: OSTerm) -> OSTerm:
        var_name, expr = let_assign
        res = os_term.OSLet(var_name, expr, rhs)
        self.ctxt.bound_vars.remove(var_name)
        return res
    
    def forall(self, params: Tuple[os_term.OSVar], body: OSTerm) -> OSTerm:
        for param in params:
            del self.ctxt.var_decls[param.name]
        return os_term.OSQuant("forall", params, body)
    
    def exists(self, params: Tuple[os_term.OSVar], body: OSTerm) -> OSTerm:
        for param in params:
            del self.ctxt.var_decls[param.name]
        return os_term.OSQuant("exists", params, body)

    def forall_in(self, param: os_term.OSVar, collection: OSTerm, body: OSTerm) -> OSTerm:
        del self.ctxt.var_decls[param.name]
        return os_term.OSQuantIn("forall", param, collection, body)

    def exists_in(self, param: os_term.OSVar, collection: OSTerm, body: OSTerm) -> OSTerm:
        del self.ctxt.var_decls[param.name]
        return os_term.OSQuantIn("exists", param, collection, body)

    def bneg(self, arg: OSTerm) -> OSTerm:
        return OSOp("!", arg)

    def bvneg(self, arg: OSTerm) -> OSTerm:
        return OSOp("~", arg)
    
    def uminus(self, arg: OSTerm) -> OSTerm:
        return OSOp("-", arg)
    
    def times(self, lhs: OSTerm, rhs: OSTerm) -> OSTerm:
        return OSOp("*", lhs, rhs)
    
    def divides(self, lhs: OSTerm, rhs: OSTerm) -> OSTerm:
        return OSOp("/", lhs, rhs)
    
    def plus(self, lhs: OSTerm, rhs: OSTerm) -> OSTerm:
        return OSOp("+", lhs, rhs)
    
    def minus(self, lhs: OSTerm, rhs: OSTerm) -> OSTerm:
        return OSOp("-", lhs, rhs)

    def bvshiftl(self, lhs: OSTerm, rhs: OSTerm) -> OSTerm:
        return OSOp("<<", lhs, rhs)
    
    def bvshiftr(self, lhs: OSTerm, rhs: OSTerm) -> OSTerm:
        return OSOp(">>", lhs, rhs)
    
    def less(self, lhs: OSTerm, rhs: OSTerm) -> OSTerm:
        return OSOp("<", lhs, rhs)

    def less_eq(self, lhs: OSTerm, rhs: OSTerm) -> OSTerm:
        return OSOp("<=", lhs, rhs)

    def greater(self, lhs: OSTerm, rhs: OSTerm) -> OSTerm:
        return OSOp(">", lhs, rhs)

    def greater_eq(self, lhs: OSTerm, rhs: OSTerm) -> OSTerm:
        return OSOp(">=", lhs, rhs)

    def eq(self, lhs: OSTerm, rhs: OSTerm) -> OSTerm:
        return OSOp("==", lhs, rhs)
    
    def not_eq(self, lhs: OSTerm, rhs: OSTerm) -> OSTerm:
        return OSOp("!=", lhs, rhs)
    
    def bvand(self, lhs: OSTerm, rhs: OSTerm) -> OSTerm:
        # print("bvand  l: ", lhs, " r: ",rhs)
        return OSOp("&", lhs, rhs)

    def bvxor(self, lhs: OSTerm, rhs: OSTerm) -> OSTerm:
        return OSOp("^", lhs, rhs)

    def bvor(self, lhs: OSTerm, rhs: OSTerm) -> OSTerm:
        return OSOp("|", lhs, rhs)
    
    def conj(self, lhs: OSTerm, rhs: OSTerm) -> OSTerm:
        return OSOp("&&", lhs, rhs)

    def disj(self, lhs: OSTerm, rhs: OSTerm) -> OSTerm:
        return OSOp("||", lhs, rhs)
    
    def impl(self, lhs: OSTerm, rhs: OSTerm) -> OSTerm:
        return OSOp("->", lhs, rhs)
    
    def os_typed_term(self, t: OSTerm) -> OSTerm:
        os_theory.check_type(self.thy, t, self.ctxt.var_decls)
        t.assert_type_checked()
        return t

    def os_localv(self, ty: OSType, name: Token) -> os_term.OSVar:
        name = str(name)
        if name in self.ctxt.var_decls:
            raise AssertionError("add_var_decl: variable %s already defined" % name)
        else:
            ty = os_theory.expand_type(self.thy, ty)
            self.ctxt.add_var_decl(name, ty)
            return os_term.OSVar(name, type=ty)
        
    def os_params(self, *vars) -> Tuple[os_term.OSVar]:
        return tuple(vars)
    
    def os_axiom_func(self, func_name: Tuple[str, Tuple[str]],
                      func_ty: OSType) -> os_struct.AxiomDef:
        func_name, ty_params = func_name
        func_ty = os_theory.expand_type(self.thy, func_ty)
        return os_struct.AxiomDef(func_name, ty_params, func_ty)
    
    def function_name(self, name: Token) -> Tuple[str, Tuple[str]]:
        return str(name), tuple()
    
    def function_name_params(self, name: Token, *params: Token) -> Tuple[str, Tuple[str]]:
        type_params = tuple(str(param) for param in params)
        # Add type parameters to context
        self.ctxt.type_params.extend(type_params)
        return str(name), type_params
    
    def os_function(self, function_name: Tuple[str, Tuple[str]], params: Tuple[os_term.OSVar],
                    ret_type: OSType, body: OSTerm) -> OSFunction:
        name, type_params = function_name
        ret_type = os_theory.expand_type(self.thy, ret_type)

        # Check body using return type, while temporarily adding type of function.
        var_ctxt = dict(self.ctxt.var_decls)
        if len(params) == 0:
            var_ctxt[name] = ret_type
        else:
            arg_types = list()
            for param in params:
                arg_types.append(param.type)
                var_ctxt[param.name] = param.type
            var_ctxt[name] = os_struct.OSFunctionType(*(arg_types + [ret_type]))
        os_theory.check_type(self.thy, body, var_ctxt, ret_type)
        body.assert_type_checked()

        res = OSFunction(name, type_params, params, ret_type, body)
        for param in params:
            del self.ctxt.var_decls[param.name]
        for type_param in type_params:
            self.ctxt.type_params.remove(type_param)
        return res

    def os_predicate(self, function_name: Tuple[str, Tuple[str]], params: Tuple[os_term.OSVar],
                     pred: OSTerm) -> OSFunction:
        return self.os_function(function_name, params, os_struct.Bool, pred)

    def tactic_branch_case(self, constr_name: Token,
                           tactic: Tactic) -> os_tactics.TacticBranch:
        constr_name = str(constr_name)
        return os_tactics.TacticBranchCase(constr_name, tuple(), tactic)

    def tactic_branch_case_params(self, constr_name: Token, *rest) -> os_tactics.TacticBranch:
        constr_name = str(constr_name)
        params, tactic = rest[:-1], rest[-1]
        params = tuple(str(param) for param in params)
        return os_tactics.TacticBranchCase(constr_name, params, tactic)
    
    def tactic_branch_case_index(self, index: Token, tactic: Tactic) -> os_tactics.TacticBranch:
        index = int(index)
        return os_tactics.TacticBranchIndex(index, tactic)

    def tactic_branch_default(self, tactic: Tactic) -> os_tactics.TacticBranch:
        return os_tactics.TacticBranchDefault(tactic)

    def induction_param_basic(self, induct_var: Token) -> os_tactics.InductionParam:
        return os_tactics.InductionParam(str(induct_var), arbitraries=tuple())
    
    def induction_param_arbitrary(self, induct_var: Token, *arbitraries: Token) -> os_tactics.InductionParam:
        arbitraries = [str(arbitrary) for arbitrary in arbitraries]
        return os_tactics.InductionParam(str(induct_var), arbitraries)

    def apply_param_basic(self, thm_name: Token) -> os_tactics.ApplyParam:
        thm_name = str(thm_name)
        return os_tactics.ApplyParam(thm_name, tuple())

    def apply_param_facts(self, thm_name: Token, *facts: Token) -> os_tactics.ApplyParam:
        thm_name = str(thm_name)
        facts = [str(fact) for fact in facts]
        return os_tactics.ApplyParam(thm_name, facts)

    def skip_tactic(self) -> Tactic:
        return os_tactics.Skip()
    
    def thm_spec(self, thm_name: Token) -> os_theory.TheoremSpec:
        return os_theory.TheoremSpec(str(thm_name), tuple())
    
    def thm_spec_type(self, thm_name: Token, *tys: OSType) -> os_theory.TheoremSpec:
        tys = [os_theory.expand_type(self.thy, ty) for ty in tys]
        return os_theory.TheoremSpec(str(thm_name), tys)

    def auto_tactic(self, *thm_spec: Tuple[os_theory.TheoremSpec]) -> Tactic:
        return os_tactics.Auto(thm_spec=thm_spec)
    
    def cases_tactic(self, expr: OSTerm, *cases: os_tactics.TacticBranch) -> Tactic:
        return os_tactics.Cases(expr, cases=cases)

    def induction_tactic(self, param: os_tactics.InductionParam, *cases: os_tactics.TacticBranch) -> Tactic:
        return os_tactics.Induction(param, cases=cases)

    def assumption_tactic(self) -> Tactic:
        return os_tactics.Assumption()

    def simplify_tactic(self) -> Tactic:
        return os_tactics.Simplify()
    
    def exists_tactic(self, *exprs: OSTerm) -> Tactic:
        return os_tactics.Exists(exprs)

    def skolemize_tactic(self, name: Token, *new_vars: os_term.OSVar) -> Tactic:
        name = str(name)
        for new_var in new_vars:
            self.ctxt.tactic_vars.add(new_var.name)
        return os_tactics.Skolemize(name, new_vars)
    
    def assert_tactic(self, name: Token, expr: OSTerm, tactic: Tactic) -> Tactic:
        return os_tactics.Assert(str(name), expr, tactic)

    def change_tactic(self, expr: OSTerm, tactic: Tactic) -> Tactic:
        return os_tactics.Change(expr, tactic)

    def split_conj_tactic(self, name: Token, *new_names: Token) -> Tactic:
        name = str(name)
        new_names = [str(new_name) for new_name in new_names]
        return os_tactics.SplitConj(name, new_names)

    def match_show_tactic(self, name: Token) -> Tactic:
        name = str(name)
        return os_tactics.MatchShow(name)
    
    def apply_theorem_tactic(self, param: os_tactics.ApplyParam) -> Tactic:
        return os_tactics.ApplyTheorem(param)

    def then_tactic(self, tactic1: Tactic, tactic2: Tactic) -> Tactic:
        return os_tactics.Then(tactic1, tactic2)
    
    def then_split_tactic(self, tactic1, *cases: os_tactics.TacticBranch) -> Tactic:
        return os_tactics.ThenSplit(tactic1, cases)

    def type_param(self, name: Token) -> str:
        name = str(name)
        # Add type variable to context
        self.ctxt.type_params.append(name)
        return name

    def fixes(self, var_name: Token, type: OSType) -> os_term.OSVar:
        # Add variable to context
        type = os_theory.expand_type(self.thy, type)
        self.ctxt.add_var_decl(str(var_name), type)
        return os_term.OSVar(str(var_name), type=type)

    def assumes(self, expr: OSTerm) -> os_query.Assumes:
        return os_query.Assumes(expr)
    
    def assumes_named(self, name: Token, expr: OSTerm) -> os_query.Assumes:
        return os_query.Assumes(expr, name=str(name))

    def assumes_trig(self, expr: OSTerm) -> os_query.Assumes:
        return os_query.Assumes(expr, is_trigger=True)
    
    def assumes_named_trig(self, name: Token, expr: OSTerm) -> os_query.Assumes:
        return os_query.Assumes(expr, name=str(name), is_trigger=True)

    def shows(self, expr: OSTerm) -> os_query.Shows:
        return os_query.Shows(expr, proof=os_tactics.Skip())
    
    def shows_trig(self, expr: OSTerm) -> os_query.Shows:
        return os_query.Shows(expr, proof=os_tactics.Skip(), is_trigger=True)

    def shows_proof(self, expr: OSTerm, proof: Tactic) -> os_query.Shows:
        for tactic_var in self.ctxt.tactic_vars:
            del self.ctxt.var_decls[tactic_var]
        self.ctxt.tactic_vars.clear()
        return os_query.Shows(expr, proof=proof)

    def shows_trig_proof(self, expr: OSTerm, proof: Tactic) -> os_query.Shows:
        for tactic_var in self.ctxt.tactic_vars:
            del self.ctxt.var_decls[tactic_var]
        self.ctxt.tactic_vars.clear()
        return os_query.Shows(expr, is_trigger=True, proof=proof)

    def os_query_def(self, query_name, *query_decls) -> os_query.Query:
        type_params: List[str] = []
        fixes: List[os_term.OSVar] = []
        assumes: List[os_query.Assumes] = []
        shows: List[os_query.Shows] = []
        for decl in query_decls:
            if isinstance(decl, str):
                type_params.append(decl)
            elif isinstance(decl, os_term.OSVar):
                fixes.append(decl)
            elif isinstance(decl, os_query.Assumes):
                assumes.append(decl)
            elif isinstance(decl, os_query.Shows):
                shows.append(decl)
        for fix in fixes:
            del self.ctxt.var_decls[fix.name]
        for type_param in type_params:
            self.ctxt.type_params.remove(type_param)
        return os_query.Query(query_name, type_params, fixes, assumes, shows)
    
    def os_typedef(self, type_name: Token, type: OSType) -> os_struct.TypeDef:
        type = os_theory.expand_type(self.thy, type)
        return os_struct.TypeDef(str(type_name), type)

    def datatype_branch_single(self, constr_name: Token) -> os_struct.DatatypeBranch:
        return os_struct.DatatypeBranch(str(constr_name))

    def datatype_branch_param(self, constr_name: Token, params: Tuple[os_term.OSVar]) -> os_struct.DatatypeBranch:
        res = os_struct.DatatypeBranch(
            str(constr_name), *((param.name, param.type) for param in params))
        for param in params:
            del self.ctxt.var_decls[param.name]
        return res
    
    def datatype_name(self, name: Token) -> Tuple[str, Tuple[str]]:
        self.ctxt.datatype_decl = str(name)
        return self.ctxt.datatype_decl, tuple()
    
    def datatype_name_params(self, name: Token, *params: Token) -> Tuple[str, Tuple[str]]:
        name = str(name)
        self.ctxt.datatype_decl = name
        type_params = tuple(str(param) for param in params)
        # Add type parameters to context
        self.ctxt.type_params.extend(type_params)
        return self.ctxt.datatype_decl, type_params

    def os_datatype(self, datatype_name: Tuple[str, Tuple[str]], *branches) -> os_struct.Datatype:
        name, params = datatype_name
        res = os_struct.Datatype(name, params, *branches)
        # Remove type parameters from context
        for param in params:
            self.ctxt.type_params.remove(param)
        return res
    
    def os_axiomtype(self, datatype_name: Tuple[str, Tuple[str]]) -> os_struct.Datatype:
        name, params = datatype_name
        res = os_struct.AxiomType(name, params)
        for param in params:
            self.ctxt.type_params.remove(param)
        return res

    def os_add_attrib(self, attrib_name: str, *th_names: str) -> os_theory.OSAttribDecl:
        return os_theory.OSAttribDecl("add", attrib_name, th_names)
    
    def os_del_attrib(self, attrib_name: str, *th_names: str) -> os_theory.OSAttribDecl:
        return os_theory.OSAttribDecl("del", attrib_name, th_names)

    def os_proof_state(self, *query_decls) -> os_tactics.ProofState:
        type_params: List[str] = []
        fixes: List[os_term.OSVar] = []
        assumes: List[os_query.Assumes] = []
        shows: List[os_query.Shows] = []
        for decl in query_decls:
            if isinstance(decl, str):
                type_params.append(decl)
            elif isinstance(decl, os_term.OSVar):
                fixes.append(decl)
            elif isinstance(decl, os_query.Assumes):
                assumes.append(decl)
            elif isinstance(decl, os_query.Shows):
                shows.append(decl)
        assert len(shows) == 1, "os_proof_state: must have exactly one conclusion"
        for fix in fixes:
            del self.ctxt.var_decls[fix.name]
        for type_param in type_params:
            self.ctxt.type_params.remove(type_param)
        return os_tactics.ProofState(
            type_params=type_params,
            fixes=fixes,
            assumes=[(assume.name, assume.prop) for assume in assumes],
            concl=shows[0].prop)

    def os_context(self, *query_decls) -> OSContext:
        # Declaration of type and variable parameters are already added.
        return self.ctxt
    
    def os_imports(self, *imports: str) -> os_theory.OSImports:
        return os_theory.OSImports(imports)
    
    def os_theory_item(self, item):
        """Main function for processing a theory item.
        
        This function performs the action corresponding to the item as it is
        read. In particular:

        - for theory imports, recursively load the imported file.
        - for struct, const, function, typedef, datatype, axiom declarations, add
          the corresponding object to the theory.
        - for queries, check proof of the query (if check_proof option is on),
          then record the query in the theory.
        - for attribute declarations, perform the corresponding add/delete action
          on the attribute.
        
        """
        if isinstance(item, os_theory.OSImports):
            # Recursively load imported theories
            for import_name in item.imports:
                load_theory_internal(import_name, self.thy, self.visited,
                                     check_proof=self.check_proof, verbose=self.verbose)
        elif isinstance(item, os_struct.Struct):
            self.print_verbose("add struct %s" % item.struct_name)
            self.thy.add_struct(item)
        elif isinstance(item, os_struct.ConstDefList):
            for const_def in item.const_defs:
                self.print_verbose("add constant %s" % const_def.const_name)
            self.thy.add_consts(item)
        elif isinstance(item, OSFunction):
            self.print_verbose("add function %s" % item.name)
            self.thy.add_function(item)
        elif isinstance(item, os_struct.TypeDef):
            self.print_verbose("add typedef %s" % item.type_name)
            self.thy.add_typedef(item)
        elif isinstance(item, os_struct.Datatype):
            self.print_verbose("add datatype %s" % item.name)
            self.thy.add_datatype(item)
        elif isinstance(item, os_struct.AxiomType):
            self.print_verbose("add axiom type %s" % item.name)
            self.thy.add_axiom_type(item)
        elif isinstance(item, os_struct.AxiomDef):
            self.print_verbose("add axiomdef %s" % item.func_name)
            self.thy.add_axiom_func(item)
        elif isinstance(item, os_query.Query):
            self.print_verbose("add query %s" % item.query_name)
            if (isinstance(self.check_proof, bool) and self.check_proof) or \
               (isinstance(self.check_proof, str) and item.query_name == self.check_proof):
                os_tactics.check_proof(self.thy, item)
            self.thy.add_query(item)
        elif isinstance(item, os_theory.OSAttribDecl):
            if item.attrib_name not in self.thy.attribute_map:
                raise AssertionError("attribute %s not found")
            attrib = self.thy.attribute_map[item.attrib_name]
            if item.operation == "add":
                for th_name in item.th_names:
                    if th_name in attrib:
                        raise AssertionError("theorem %s already has attribute %s" % (
                            th_name, item.attrib_name))
                    attrib.append(th_name)
            elif item.operation == "del":
                for th_name in item.th_names:
                    if th_name not in attrib:
                        raise AssertionError("theorem %s not in attribute %s" % (
                            th_name, item.attrib_name))
                    attrib.remove(th_name)
            else:
                raise AssertionError("unknown attribute operation: %s" % item.operation)
        else:
            raise AssertionError("unknown declaration type: %s" % type(item))

def type_parser(thy: OSTheory, ctxt: OSContext):
    return Lark(os_verify_grammar, start="os_type", parser="lalr",
                transformer=OSVerifyTransformer(thy, ctxt=ctxt))

def term_parser(thy: OSTheory, ctxt: OSContext):
    return Lark(os_verify_grammar, start="os_typed_term", parser="lalr",
                transformer=OSVerifyTransformer(thy, ctxt=ctxt))

def struct_parser(thy: OSTheory):
    return Lark(os_verify_grammar, start="os_struct_def", parser="lalr",
                transformer=OSVerifyTransformer(thy))

def consts_parser(thy: OSTheory):
    return Lark(os_verify_grammar, start="os_consts", parser="lalr",
                transformer=OSVerifyTransformer(thy))

def function_parser(thy: OSTheory):
    return Lark(os_verify_grammar, start="os_function", parser="lalr",
                transformer=OSVerifyTransformer(thy))

def predicate_parser(thy: OSTheory):
    return Lark(os_verify_grammar, start="os_predicate", parser="lalr",
                transformer=OSVerifyTransformer(thy))

def query_parser(thy: OSTheory):
    return Lark(os_verify_grammar, start="os_query_def", parser="lalr",
                transformer=OSVerifyTransformer(thy))

def typedef_parser(thy: OSTheory):
    return Lark(os_verify_grammar, start="os_typedef", parser="lalr",
                transformer=OSVerifyTransformer(thy))

def axiomfunc_parser(thy: OSTheory):
    return Lark(os_verify_grammar, start="os_axiom_func", parser="lalr",
                transformer=OSVerifyTransformer(thy))

def datatype_parser(thy: OSTheory):
    return Lark(os_verify_grammar, start="os_datatype", parser="lalr",
                transformer=OSVerifyTransformer(thy))

def proof_state_parser(thy: OSTheory):
    return Lark(os_verify_grammar, start="os_proof_state", parser="lalr",
                transformer=OSVerifyTransformer(thy))

def context_parser(thy: OSTheory):
    return Lark(os_verify_grammar, start="os_context", parser="lalr",
                transformer=OSVerifyTransformer(thy))

def imports_parser(thy: OSTheory):
    return Lark(os_verify_grammar, start="os_imports", parser="lalr",
                transformer=OSVerifyTransformer(thy))

def theory_items_parser(thy: OSTheory, visited: Set[str], check_proof: bool, verbose: bool):
    return Lark(os_verify_grammar, start="os_theory_items", parser="lalr",
                transformer=OSVerifyTransformer(thy, visited=visited, check_proof=check_proof,
                                                verbose=verbose))

def parse_type(thy: OSTheory, ctxt: OSContext, s: str) -> OSType:
    return type_parser(thy, ctxt).parse(s)

def parse_term(thy: OSTheory, ctxt: OSContext, s: str) -> OSTerm:
    return term_parser(thy, ctxt).parse(s)

def parse_struct(thy: OSTheory, s: str) -> os_struct.Struct:
    return struct_parser(thy).parse(s)

def parse_consts(thy: OSTheory, s: str) -> os_struct.ConstDefList:
    return consts_parser(thy).parse(s)

def parse_function(thy: OSTheory, s: str) -> OSFunction:
    return function_parser(thy).parse(s)

def parse_predicate(thy: OSTheory, s: str) -> OSFunction:
    return predicate_parser(thy).parse(s)

def parse_query(thy: OSTheory, s: str) -> os_query.Query:
    return query_parser(thy).parse(s)

def parse_typedef(thy: OSTheory, s: str) -> os_struct.TypeDef:
    return typedef_parser(thy).parse(s)

def parse_axiomfunc(thy: OSTheory, s: str) -> os_struct.AxiomDef:
    return axiomfunc_parser(thy).parse(s)

def parse_datatype(thy: OSTheory, s: str) -> os_struct.Datatype:
    return datatype_parser(thy).parse(s)

def parse_proof_state(thy: OSTheory, s: str) -> os_tactics.ProofState:
    return proof_state_parser(thy).parse(s)

def parse_context(thy: OSTheory, s: str) -> OSContext:
    return context_parser(thy).parse(s)

def parse_imports(thy: OSTheory, s: str) -> os_theory.OSImports:
    return imports_parser(thy).parse(s)

def parse_theory_items(thy: OSTheory, s: str, visited: Set[str], *, check_proof: bool, verbose: bool):
    return theory_items_parser(thy, visited, check_proof, verbose).parse(s)


def read_theory_file(theory_name: str) -> str:
    """Read file content for the given theory name.
    
    Currently, we only look up the file in the theory directory.
    Looking for the file in more paths can be added later.

    Parameters
    ----------
    theory_name : str
        name of the theory file to be read, no extension necessary
        (assumed to be .thy).

    Returns
    -------
    str
        string content of the file.

    """
    with open("./osverify/theory/%s.thy" % theory_name) as f:
        return f.read()


def load_theory_internal(theory_name: str, thy: OSTheory, visited: Set[str], *,
                         check_proof=False, verbose=False):
    """Load of theory file with the given name, internal version.

    Parameters
    ----------
    theory_name : str
        name of the theory to be parsed.
    thy : OSTheory
        base theory. Content of the file is added onto this theory. Modified
        by this function.
    visited : Set[str]
        set of theories that are already visited. Modified by this function.
    check_proof : bool, default to False
        whether to check proof during loading.
    verbose : bool, default to False
        whether to print debugging information during load

    """
    if theory_name in visited:
        return  # theory already loaded

    visited.add(theory_name)

    if verbose:
        print("read file %s" % theory_name)
    content = read_theory_file(theory_name)
    parse_theory_items(thy, content, visited, check_proof=check_proof, verbose=verbose)


def load_theory(theory_name: str, *,
                verbose: bool = False,
                check_proof: Union[bool, str] = False) -> OSTheory:
    """Load theory file with the given name.
    
    Parameters
    ----------
    theory_name : str
        name of the theory to be parsed.
    verbose : bool, default to False
        whether to print debugging information during load.
    check_proof : Union[bool, str], default to False
        for boolean values, it means whether to check proof during loading.
        for string values, only proof for that query is checked.

    Returns
    -------
    OSTheory
        result of loading the theory files.
    
    """
    thy = os_theory.OSTheory()
    visited = set()
    load_theory_internal(theory_name, thy, visited, check_proof=check_proof,
                         verbose=verbose)
    return thy
