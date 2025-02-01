"""Parser for OS verification"""

import os
from lark import Lark, Transformer, v_args, Token
from typing import Optional, Union
import time

from osverify import os_struct
from osverify import os_term
from osverify import os_query
from osverify import os_theory
from osverify import os_tactics
from osverify import os_fixp
from osverify import os_seplogic
from osverify import os_seq
from osverify.os_theory import OSTheory
from osverify.os_struct import OSType
from osverify.os_term import OSTerm, OSOp, VarContext, GenField
from osverify.os_tactics import Tactic
from osverify import auto_tactics
from osverify.os_seplogic import SepAssertion
from osverify import os_z3wrapper
from osverify import os_model
from osverify.graph import ClassificationGraph


os_verify_grammar = r"""
    // Primitive types
    ?os_prim_type: "bool" -> bool_type
            | "int" -> int_type
            | "int8u" -> int8u_type
            | "int16u" -> int16u_type
            | "int32u" -> int32u_type
            | "int64u" -> int64u_type
            | "int8" -> int8_type
            | "int16" -> int16_type
            | "int32" -> int32_type
            | "int64" -> int64_type

    // General types
    ?os_atom_type: os_prim_type
            | CNAME -> os_hlevel_type
            | "?" CNAME -> os_sch_type
            | CNAME "<" os_type ("," os_type)* ">" -> os_hlevel_param_type
            | "(" os_type ")"

    ?os_type: (os_atom_type "->")+ os_atom_type -> os_fun_type
            | os_atom_type

    // Annotation on fields
    ?annotation: "binary" -> binary_annotation
            | "octal" -> octal_annotation
            | "hex" -> hex_annotation

    // Field of a structure
    ?os_field: os_type CNAME ("[" annotation ("," annotation)* "]")?

    // Structure definition
    ?os_struct_def: "struct" CNAME "{" (os_field ";")* "}"

    // Single constant definition
    ?os_const: "const" os_type CNAME "=" os_term ";"

    // Auxiliary for structure update
    ?field_update: CNAME ":=" os_term

    ?ori_struct: CNAME -> ori_struct_name
        | "[[" os_typed_term "]]" -> ori_struct_expr

    // Auxiliary for structure value
    ?struct_field: CNAME ":" os_term

    ?struct_name: CNAME -> struct_name

    // Auxiliary for let expression
    ?let_assign: CNAME "=" os_typed_term

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

    // Generalized field updates
    ?gen_field: CNAME -> atom_gen_field
            | gen_field "[" os_term "]" -> index_gen_field
            | gen_field "." CNAME -> field_get_gen_field

    ?os_atom: CNAME -> vname
            | "?" CNAME -> sch_vname
            | os_atom "@" os_type -> atom_with_type
            | INT -> number
            | ori_struct "{" field_update ("," field_update)* "}" -> struct_update
            | ori_struct "{|" gen_field ":=" os_term "|}" -> struct_update_gen
            | struct_name "{{" struct_field ("," struct_field)* "}}" -> struct_val
            | CNAME "(" os_term ("," os_term)* ")" -> function_app
            | "(" os_term ")"                                // Parenthesis
            | "|" os_atom "|"  -> seq_length                 // Sequence length
            | os_atom "[" os_term "]" -> seq_index           // Sequence indexing
            | os_atom "++" os_atom -> seq_append             // Sequence append
            | os_atom "::" os_atom -> seq_cons               // Sequence connect
            | os_atom "[" os_term ":" os_term "]" -> seq_slice // Sequence slice
            | "[" "]" -> seq_literal_empty                   // Sequence literal
            | "[" os_term ("," os_term)* "]" -> seq_literal  // Empty sequence literal
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
         
    ?power:  power "**" negation -> power              
            | negation                            // priority 89
    
    ?times: times "*" power -> times
            | times "/" power -> divides         
            | times "%" power ->  modulo
            | power                             // priority 87

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

    // Definitions for separation logic
    ?sep_atom: CNAME "(" os_typed_term ("," os_typed_term)* ")"   -> sep_fun

    ?sep: sep_atom (";" sep_atom)*                 -> sep_conj
   
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

    ?tactic_atom: "skip" -> skip_tactic
            | "admit" -> admit_tactic
            | "auto" -> auto_tactic
            | "seq_auto" -> seq_auto_tactic
            | "cases" "(" os_typed_term ")" "{" (tactic_branch ";")* "}" -> cases_tactic
            | "induction" "(" induction_param ")" "{" (tactic_branch ";")* "}" -> induction_tactic
            | "induction_func" "(" CNAME ")" -> induction_func_tactic
            | "assumption" -> assumption_tactic
            | "rewrite" CNAME -> rewrite_tactic
            | "let" "(" CNAME "=" os_typed_term ")" -> define_var_tactic
            | "exists" "(" os_typed_term ("," os_typed_term)* ")" -> exists_tactic
            | "specialize" CNAME "(" os_typed_term ("," os_typed_term)* ")" -> specialize_tactic
            | "skolemize" "(" CNAME "," "[" os_localv ("," os_localv)* "]" ")" -> skolemize_tactic
            | "intros" "[" os_localv ("," os_localv)* "]" -> intros_tactic
            | "assert" "(" CNAME ":" os_typed_term ")" "{" tactic "}" -> assert_tactic
            | "change" "(" os_typed_term ")" "{" tactic "}" -> change_tactic
            | "split_conj" "(" CNAME "," "[" CNAME ("," CNAME)* "]" ")" -> split_conj_tactic
            | "split_goal" -> split_goal_tactic
            | "match_show" "(" CNAME ")" -> match_show_tactic
            | "apply_theorem" "(" apply_param ")" -> apply_theorem_tactic
            | "apply" "(" CNAME ")" -> apply_tactic

    ?tactic: tactic_atom
            | tactic_atom ";;" tactic -> then_tactic
            | tactic_atom "{" (tactic_branch ";")* "}" -> then_split_tactic

    // Query declarations
    ?type_param: "type" CNAME -> type_param

    ?fixes: "fixes" CNAME ":" os_type

    ?assumes: "assumes" os_typed_term -> assumes
            | "assumes" CNAME ":" os_typed_term -> assumes_named
            | "assumes" "[trigger]" os_typed_term -> assumes_trigger
            | "assumes" CNAME "[trigger]" ":" os_typed_term -> assumes_named_trigger

    ?shows: "shows" os_typed_term -> shows
            | "shows" "[trigger]" os_typed_term -> shows_trigger
            | "shows" os_typed_term "proof" "{" tactic "}" -> shows_proof
            | "shows" "[trigger]" os_typed_term "proof" "{" tactic "}" -> shows_trigger_proof

    ?query_decl: type_param | fixes | assumes | shows

    // Query definition
    ?os_query_def: "query" CNAME "{" query_decl (";" query_decl)* "}"

    ?os_axiom_def: "axiom" CNAME "{" query_decl (";" query_decl)* "}" 

    // Type alias definition
    ?os_typedef: "typedef" CNAME "=" os_type ";"

    // Datatype definition
    ?datatype_branch: CNAME -> datatype_branch_single
            | CNAME "(" os_params ")" -> datatype_branch_param

    ?datatype_name: CNAME -> datatype_name
            | CNAME "<" CNAME ("," CNAME)* ">" -> datatype_name_params

    ?os_datatype: "enum" datatype_name "=" datatype_branch ("|" datatype_branch)*
            | "axiomtype" datatype_name -> os_axiomtype

    ?os_attrib_decl: "add_attrib" CNAME "for" CNAME ("," CNAME)* -> os_add_attrib
            | "del_attrib" CNAME "for" CNAME ("," CNAME)* -> os_del_attrib

    ?os_imports: "imports" CNAME ("," CNAME)* -> os_imports

    ?os_theory_item: os_imports -> os_theory_item
            | os_struct_def -> os_theory_item
            | os_const -> os_theory_item
            | os_function -> os_theory_item
            | os_predicate -> os_theory_item
            | os_query_def -> os_theory_item
            | os_axiom_def -> os_theory_item
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
                 ctxt: Optional[VarContext] = None,
                 visited: Optional[set[str]] = None,
                 check_proof: Union[bool, str] = False,
                 print_time=False,
                 verbose=False):
        self.thy = thy
        if ctxt is None:
            self.ctxt = VarContext()
        else:
            assert isinstance(ctxt, VarContext), \
                "input context to parser should be VarContext"
            self.ctxt = ctxt

        # Temporary label for recursive datatype
        self.datatype_decl: Optional[str] = None

        # Default structure
        self.default_struct: list[str] = list()

        # List of declared tactic variables
        self.tactic_vars: set[str] = set()

        if visited is None:
            visited = set()
        self.visited = visited
        self.check_proof = check_proof

        # Print time for each query
        self.print_time = print_time

        # Extra printing statements
        self.verbose = verbose

    def print_verbose(self, s: str):
        if self.verbose:
            print(s)

    def lookup_field(self, field_name: str) -> Optional[OSType]:
        """Return type of a field from default structure."""
        if not self.default_struct:
            return None  # no structure is set

        if self.default_struct[-1] not in self.thy.structs:
            raise AssertionError(
                "lookup_field: default structure %s not found in theory" \
                    % self.default_struct[-1])

        struct = self.thy.structs[self.default_struct[-1]]
        if field_name not in struct.field_map:
            return None  # field not found

        return struct.field_map[field_name]

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
    
    def int64u_type(self) -> OSType:
        return os_struct.OSPrimType("int64u")

    def int8_type(self) -> OSType:
        return os_struct.OSPrimType("int8")

    def int16_type(self) -> OSType:
        return os_struct.OSPrimType("int16")

    def int32_type(self) -> OSType:
        return os_struct.OSPrimType("int32")

    def int64_type(self) -> OSType:
        return os_struct.OSPrimType("int64")
    
    def os_hlevel_type(self, name: Token) -> OSType:
        name = str(name)
        if self.thy.is_defined_type(name):
            return os_struct.OSHLevelType(name)
        elif name in self.thy.structs:
            return os_struct.OSStructType(name)
        elif name == self.datatype_decl:
            return os_struct.OSHLevelType(name)
        elif name in self.ctxt.type_params:
            return os_struct.OSBoundType(name)
        else:
            raise AssertionError("Type %s not found" % name)
    
    def os_hlevel_param_type(self, name: Token, *params: OSType) -> OSType:
        name = str(name)
        if self.thy.is_defined_type(name):
            return os_struct.OSHLevelType(name, *params)
        elif name == self.datatype_decl:
            return os_struct.OSHLevelType(name, *params)
        elif name in self.thy.axiom_types:
            return os_struct.OSHLevelType(name, *params)
        else:
            raise AssertionError("Type %s not found" % name)
    
    def os_sch_type(self, name: Token) -> OSType:
        return os_struct.OSBoundType("?" + str(name))

    def os_fun_type(self, *tys: OSType) -> OSType:
        return os_struct.OSFunctionType(*tys)

    def binary_annotation(self) -> str:
        return "binary"

    def octal_annotation(self) -> str:
        return "octal"

    def hex_annotation(self) -> str:
        return "hex"

    def os_field(self, type: OSType, field_name: Token, *annotations: str) -> os_struct.StructField:
        return os_struct.StructField(
            os_theory.expand_type(self.thy, type), str(field_name), annotations)

    def os_struct_def(self, struct_name: Token, *fields) -> os_struct.Struct:
        return os_struct.Struct(str(struct_name), fields)

    def os_const(self, type: OSType, const_name: Token, body: OSTerm) -> os_fixp.OSFunction:
        os_theory.check_type(self.thy, body, self.ctxt, type)
        return os_fixp.OSFunction(str(const_name), [], [], type, body)

    def vname(self, name: Token) -> OSTerm:
        name = str(name)
        if name == 'true':
            return os_term.OSNumber(True)
        elif name == 'false':
            return os_term.OSNumber(False)
        elif name == 'default':
            # Default value for type
            return os_term.OSFun(name, type=None)
        elif name in self.thy.constr_types:
            # Constructor
            return os_term.OSFun(name)
        elif self.ctxt.contains_var(name):
            # Declared variable
            return os_term.OSVar(name)
        elif name in self.thy.fixps:
            # Declared function
            fixp = self.thy.fixps[name]
            assert len(fixp.params) == 0, "vname: function %s has arguments" % name
            return os_term.OSFun(fixp.name, type=fixp.ret_type)
        else:
            # Field of default structure
            ty = self.lookup_field(name)
            if ty is None:
                raise AssertionError("Variable %s not found" % name)
            else:
                return os_term.OSVar(name, type=ty)
    
    def sch_vname(self, name: Token) -> OSTerm:
        return os_term.OSVar('?' + str(name))

    def atom_with_type(self, expr: OSTerm, ty: OSType) -> OSTerm:
        expr.type = os_theory.expand_type(self.thy, ty)
        return expr

    def number(self, val: Token) -> OSTerm:
        return os_term.OSNumber(int(val))

    def field_update(self, field_name: Token, expr: OSTerm) -> OSTerm:
        field_name = str(field_name)
        # Check field with the given name exists
        if self.lookup_field(field_name) is None:
            raise AssertionError("field %s is not found" % field_name)
        return os_term.FieldUpdate(field_name, expr)

    def ori_struct_name(self, name: Token) -> OSTerm:
        name = str(name)
        if not self.ctxt.contains_var(name):
            raise AssertionError(f"struct_update: variable {name} not found")
        var_type = self.ctxt.get_var_type(name)
        if not isinstance(var_type, os_struct.OSStructType):
            raise AssertionError(
                f"struct_update: original term {name} is not of structure type, found {var_type}")
        self.default_struct.append(var_type.name)
        return os_term.OSVar(name)

    def ori_struct_expr(self, expr: OSTerm) -> OSTerm:
        # Set default structure when parsing an update
        ty = expr.type
        if not isinstance(ty, os_struct.OSStructType):
            raise AssertionError("struct_update: original term %s is not of structure type" % ty.name)
        self.default_struct.append(ty.name)
        return expr
    
    def struct_update(self, ori_struct: OSTerm, *updates) -> OSTerm:
        # Clear default structure after parsing an update
        del self.default_struct[-1]

        return os_term.OSStructUpdate(ori_struct, updates)
    
    def struct_update_gen(self, ori_struct: OSTerm, gen_field: GenField, expr: OSTerm) -> OSTerm:
        # Clear default structure after parsing an update
        del self.default_struct[-1]

        return os_term.OSStructUpdateGen(ori_struct, gen_field, expr)

    def struct_field(self, field_name: Token, expr: OSTerm) -> tuple[str, OSTerm]:
        field_name = str(field_name)
        # Check field with the given name exists
        if self.lookup_field(field_name) is None:
            raise AssertionError("field %s is not found" % field_name)
        return field_name, expr

    def struct_name(self, name: Token) -> str:
        # Set default structure when parsing a structure value
        name = str(name)
        if name not in self.thy.structs:
            raise AssertionError("struct_val: structure %s not found" % name)
        self.default_struct.append(name)
        return name

    def struct_val(self, name: str, *fields: tuple[str, OSTerm]) -> OSTerm:
        # Clear default structure after parsing a value
        del self.default_struct[-1]

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

    def seq_length(self, l: OSTerm) -> OSTerm:
        return os_term.OSFun("seq_length", l)

    def seq_index(self, expr: OSTerm, index: OSTerm) -> OSTerm:
        return os_term.OSFun("seq_index", index, expr)

    def seq_append(self, l1: OSTerm, l2: OSTerm) -> OSTerm:
        return os_term.OSFun("seq_append", l1, l2)

    def seq_cons(self, v: OSTerm, l: OSTerm) -> OSTerm:
        return os_term.OSFun("seq_cons", v, l)

    def seq_slice(self, l: OSTerm, i: OSTerm, j : OSTerm) -> OSTerm:
        return os_term.OSFun("seq_slice", i, j, l)

    def seq_literal_empty(self) -> OSTerm:
        return os_term.seq_literal()

    def seq_literal(self, *ts: OSTerm) -> OSTerm:
        return os_term.seq_literal(*ts)

    def member_get(self, expr: OSTerm, field_name: Token) -> OSTerm:
        return os_term.FieldGet(expr, str(field_name))

    def case_struct_field(self, field_name: Token, pat: OSTerm) -> tuple[str, OSTerm]:
        field_name = str(field_name)
        # Check field with the given name exists
        if self.lookup_field(field_name) is None:
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
            self.ctxt.add_var_decl(name)
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

    def case_pat_struct(self, struct_name: str, *vals: tuple[str, OSTerm]) -> OSTerm:
        # Clear default structure after parsing a value
        del self.default_struct[-1]

        return os_term.OSStructVal(struct_name, vals)

    def case_branch(self, pattern: OSTerm, expr: OSTerm) -> os_term.OSSwitchBranch:
        _, bound_vars = pattern.get_vars()
        for var in bound_vars:
            self.ctxt.del_var_decl(var.name)
        return os_term.OSSwitchBranchCase(pattern, expr)

    def default_branch(self, expr: os_term.OSTerm) -> os_term.OSSwitchBranch:
        return os_term.OSSwitchBranchDefault(expr)

    def switch_case(self, var_name: str, *branches: os_term.OSSwitchBranch) -> OSTerm:
        return os_term.OSSwitch(var_name, branches)

    def ite(self, cond: OSTerm, if_branch: OSTerm, else_branch: OSTerm) -> OSTerm:
        return os_term.OSFun("ite", cond, if_branch, else_branch)

    def let_assign(self, var_name: Token, expr: OSTerm):
        var_name = str(var_name)
        self.ctxt.add_var_decl(var_name, expr.type)
        return var_name, expr

    def let_in(self, let_assign, expr: OSTerm) -> OSTerm:
        var_name, rhs = let_assign
        res = os_term.OSLet(var_name, rhs, expr)
        self.ctxt.del_var_decl(var_name)
        return res
    
    def forall(self, params: tuple[os_term.OSVar], body: OSTerm) -> OSTerm:
        for param in params:
            self.ctxt.del_var_decl(param.name)
        return os_term.OSQuant("forall", params, body)
    
    def exists(self, params: tuple[os_term.OSVar], body: OSTerm) -> OSTerm:
        for param in params:
            self.ctxt.del_var_decl(param.name)
        return os_term.OSQuant("exists", params, body)

    def forall_in(self, param: os_term.OSVar, collection: OSTerm, body: OSTerm) -> OSTerm:
        self.ctxt.del_var_decl(param.name)
        return os_term.OSQuantIn("forall", param, collection, body)

    def exists_in(self, param: os_term.OSVar, collection: OSTerm, body: OSTerm) -> OSTerm:
        self.ctxt.del_var_decl(param.name)
        return os_term.OSQuantIn("exists", param, collection, body)

    def bneg(self, arg: OSTerm) -> OSTerm:
        return OSOp("!", arg)

    def bvneg(self, arg: OSTerm) -> OSTerm:
        return OSOp("~", arg)
    
    def uminus(self, arg: OSTerm) -> OSTerm:
        return OSOp("-", arg)

    def power(self, lhs: OSTerm, rhs: OSTerm) -> OSTerm:
        return OSOp("**", lhs, rhs)

    def times(self, lhs: OSTerm, rhs: OSTerm) -> OSTerm:
        return OSOp("*", lhs, rhs)

    def divides(self, lhs: OSTerm, rhs: OSTerm) -> OSTerm:
        return OSOp("/", lhs, rhs)

    def modulo(self, lhs: OSTerm, rhs: OSTerm) -> OSTerm:
        return OSOp("%", lhs, rhs)

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
        os_theory.check_type(self.thy, t, self.ctxt)
        t.assert_type_checked()
        return t

    def sep_fun(self, func_name: Token, *args: OSTerm) -> SepAssertion:
        return os_seplogic.SepFun(str(func_name), *args)

    def sep_conj(self, *parts: SepAssertion) -> os_seplogic.SepConj:
        return os_seplogic.SepConj(*parts)

    def os_localv(self, ty: OSType, name: Token) -> os_term.OSVar:
        name = str(name)
        ty = os_theory.expand_type(self.thy, ty)
        self.ctxt.add_var_decl(name, ty)
        return os_term.OSVar(name, type=ty)
        
    def os_params(self, *vars) -> tuple[os_term.OSVar]:
        return tuple(vars)
    
    def atom_gen_field(self, field_name: Token) -> GenField:
        field_name = str(field_name)
        # Check field with the given name exists
        if self.lookup_field(field_name) is None:
            raise AssertionError("field %s is not found" % field_name)
        return os_term.AtomGenField(field_name)

    def index_gen_field(self, base: GenField, index: OSTerm):
        return os_term.IndexGenField(base, index)

    def field_get_gen_field(self, base: GenField, name: Token):
        return os_term.FieldGetGenField(base, str(name))

    def os_axiom_func(self, func_name: tuple[str, tuple[str]],
                      func_ty: OSType) -> os_struct.AxiomDef:
        func_name, ty_params = func_name
        func_ty = os_theory.expand_type(self.thy, func_ty)
        res = os_struct.AxiomDef(func_name, ty_params, func_ty)
        # Remove type parameters from context
        for param in ty_params:
            self.ctxt.type_params.remove(param)
        return res
    
    def function_name(self, name: Token) -> tuple[str, tuple[str]]:
        return str(name), tuple()
    
    def function_name_params(self, name: Token, *params: Token) -> tuple[str, tuple[str]]:
        type_params = tuple(str(param) for param in params)
        # Add type parameters to context
        self.ctxt.type_params.extend(type_params)
        return str(name), type_params
    
    def os_function(self, function_name: tuple[str, tuple[str]],
                    params: tuple[os_term.OSVar],
                    ret_type: OSType, body: OSTerm) -> os_fixp.OSFunction:
        name, type_params = function_name
        ret_type = os_theory.expand_type(self.thy, ret_type)

        # Check body using return type, while temporarily adding type of function.
        if len(params) == 0:
            self.ctxt.add_var_decl(name, ret_type)
        else:
            arg_types = list()
            for param in params:
                arg_types.append(param.type)
                self.ctxt.add_var_decl(param.name, param.type)
            self.ctxt.add_var_decl(name, os_struct.OSFunctionType(*(arg_types + [ret_type])))
        os_theory.check_type(self.thy, body, self.ctxt, ret_type)
        body.assert_type_checked()

        res = os_fixp.OSFunction(name, type_params, params, ret_type, body)
        self.ctxt.del_var_decl(name)
        for param in params:
            self.ctxt.del_var_decl(param.name)
        for type_param in type_params:
            self.ctxt.type_params.remove(type_param)
        return res

    def os_predicate(self, function_name: tuple[str, tuple[str]],
                     params: tuple[os_term.OSVar],
                     pred: OSTerm) -> os_fixp.OSFunction:
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
    
    def admit_tactic(self) -> Tactic:
        return os_tactics.Admit()

    def auto_tactic(self) -> Tactic:
        return os_tactics.Auto()
    
    def seq_auto_tactic(self) -> Tactic:
        return os_seq.SeqAuto()

    def cases_tactic(self, expr: OSTerm, *cases: os_tactics.TacticBranch) -> Tactic:
        return os_tactics.Cases(expr, cases=cases)

    def induction_tactic(self, param: os_tactics.InductionParam, *cases: os_tactics.TacticBranch) -> Tactic:
        return os_tactics.Induction(param, cases=cases)

    def induction_func_tactic(self, func_name: Token) -> Tactic:
        return os_tactics.InductionFunc(str(func_name))

    def assumption_tactic(self) -> Tactic:
        return os_tactics.Assumption()

    def rewrite_tactic(self, th_name: Token) -> Tactic:
        return os_tactics.Rewrite(str(th_name))

    def define_var_tactic(self, var_name: Token, expr: OSTerm) -> Tactic:
        var_name = str(var_name)
        if self.ctxt.contains_var(var_name):
            raise AssertionError(f"let: variable {var_name} already used")
        self.ctxt.add_var_decl(var_name, expr.type)
        self.tactic_vars.add(var_name)
        return os_tactics.DefineVar(var_name, expr)

    def exists_tactic(self, *exprs: OSTerm) -> Tactic:
        return os_tactics.Exists(exprs)

    def specialize_tactic(self, name: Token, *exprs: OSTerm) -> Tactic:
        return os_tactics.Specialize(str(name), exprs)

    def skolemize_tactic(self, name: Token, *new_vars: os_term.OSVar) -> Tactic:
        name = str(name)
        for new_var in new_vars:
            self.tactic_vars.add(new_var.name)
        return os_tactics.Skolemize(name, new_vars)
    
    def intros_tactic(self, *new_vars: os_term.OSVar) -> Tactic:
        for new_var in new_vars:
            self.tactic_vars.add(new_var.name)
        return os_tactics.Intros([var.name for var in new_vars])
    
    def assert_tactic(self, name: Token, expr: OSTerm, tactic: Tactic) -> Tactic:
        return os_tactics.Assert(str(name), expr, tactic)

    def change_tactic(self, expr: OSTerm, tactic: Tactic) -> Tactic:
        return os_tactics.Change(expr, tactic)

    def split_conj_tactic(self, name: Token, *new_names: Token) -> Tactic:
        name = str(name)
        new_names = [str(new_name) for new_name in new_names]
        return os_tactics.SplitConj(name, new_names)

    def split_goal_tactic(self) -> Tactic:
        return os_tactics.SplitGoal()

    def match_show_tactic(self, name: Token) -> Tactic:
        name = str(name)
        return os_tactics.MatchShow(name)
    
    def apply_theorem_tactic(self, param: os_tactics.ApplyParam) -> Tactic:
        return os_tactics.ApplyTheorem(param)

    def apply_tactic(self, name: Token) -> Tactic:
        name = str(name)
        if hasattr(os_seq, name):
            return getattr(os_seq, name)()
        if hasattr(os_tactics, name):
            return getattr(os_tactics, name)()
        if hasattr(auto_tactics, name):
            return getattr(auto_tactics, name)()
        raise AssertionError("Name %s not found")

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
        return os_query.Assumes(expr, generation=0, conds=tuple(),
                                meta=os_query.Meta(initial_form=expr))
    
    def assumes_named(self, name: Token, expr: OSTerm) -> os_query.Assumes:
        return os_query.Assumes(expr, generation=0, conds=tuple(), name=str(name),
                                meta=os_query.Meta(initial_form=expr))

    def assumes_trigger(self, expr: OSTerm) -> os_query.Assumes:
        return os_query.Assumes(expr, generation=0, conds=tuple(),
                                meta=os_query.Meta(initial_form=expr, is_trigger=True))
    
    def assumes_named_trigger(self, name: Token, expr: OSTerm) -> os_query.Assumes:
        return os_query.Assumes(expr, generation=0, conds=tuple(), name=str(name),
                                meta=os_query.Meta(initial_form=expr, is_trigger=True))

    def shows(self, expr: OSTerm) -> os_query.Shows:
        return os_query.Shows(expr, proof=os_tactics.Skip(), meta=os_query.Meta(initial_form=expr))
    
    def shows_trigger(self, expr: OSTerm) -> os_query.Shows:
        return os_query.Shows(expr, proof=os_tactics.Skip(),
                              meta=os_query.Meta(initial_form=expr, is_trigger=True))

    def shows_proof(self, expr: OSTerm, proof: Tactic) -> os_query.Shows:
        for tactic_var in self.tactic_vars:
            self.ctxt.del_var_decl(tactic_var)
        self.tactic_vars.clear()
        return os_query.Shows(expr, proof=proof, meta=os_query.Meta(initial_form=expr))

    def shows_trigger_proof(self, expr: OSTerm, proof: Tactic) -> os_query.Shows:
        for tactic_var in self.tactic_vars:
            self.ctxt.del_var_decl(tactic_var)
        self.tactic_vars.clear()
        return os_query.Shows(expr, proof=proof,
                              meta=os_query.Meta(initial_form=expr, is_trigger=True))

    def mk_os_query(self, query_name, query_decls, *, is_axiom) -> os_query.Query:
        type_params: list[str] = []
        fixes: list[os_term.OSVar] = []
        assumes: list[os_query.Assumes] = []
        shows: list[os_query.Shows] = []
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
            self.ctxt.del_var_decl(fix.name)
        for type_param in type_params:
            self.ctxt.type_params.remove(type_param)
        return os_query.Query(query_name, type_params, fixes, assumes, shows,
                              is_axiom=is_axiom)

    def os_query_def(self, query_name, *query_decls) -> os_query.Query:
        return self.mk_os_query(query_name, query_decls, is_axiom=False)
    
    def os_axiom_def(self, query_name, *query_decls) -> os_query.Query:
        return self.mk_os_query(query_name, query_decls, is_axiom=True)

    def os_typedef(self, type_name: Token, type: OSType) -> os_struct.TypeDef:
        type = os_theory.expand_type(self.thy, type)
        return os_struct.TypeDef(str(type_name), type)

    def datatype_branch_single(self, constr_name: Token) -> os_struct.DatatypeBranch:
        return os_struct.DatatypeBranch(str(constr_name))

    def datatype_branch_param(self, constr_name: Token,
                              params: tuple[os_term.OSVar]) -> os_struct.DatatypeBranch:
        res = os_struct.DatatypeBranch(
            str(constr_name), *((param.name, param.type) for param in params))
        for param in params:
            self.ctxt.del_var_decl(param.name)
        return res
    
    def datatype_name(self, name: Token) -> tuple[str, tuple[str]]:
        self.datatype_decl = str(name)
        return self.datatype_decl, tuple()
    
    def datatype_name_params(self, name: Token, *params: Token) -> tuple[str, tuple[str]]:
        name = str(name)
        self.datatype_decl = name
        type_params = tuple(str(param) for param in params)
        # Add type parameters to context
        self.ctxt.type_params.extend(type_params)
        return self.datatype_decl, type_params

    def os_datatype(self, datatype_name: tuple[str, tuple[str]], *branches) -> os_struct.Datatype:
        name, params = datatype_name
        res = os_struct.Datatype(name, params, *branches)
        # Remove type parameters from context
        for param in params:
            self.ctxt.type_params.remove(param)
        return res
    
    def os_axiomtype(self, datatype_name: tuple[str, tuple[str]]) -> os_struct.Datatype:
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
        type_params: list[str] = []
        fixes: list[os_term.OSVar] = []
        assumes: list[os_query.Assumes] = []
        shows: list[os_query.Shows] = []
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
            self.ctxt.del_var_decl(fix.name)
        for type_param in type_params:
            self.ctxt.type_params.remove(type_param)
        return os_tactics.ProofState(
            type_params=type_params,
            fixes=fixes,
            assumes=assumes,
            concl=shows[0],
            graph=None
        )

    def os_context(self, *query_decls) -> VarContext:
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
        elif isinstance(item, os_fixp.OSFunction):
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
            if item.is_axiom:
                self.print_verbose("add axiom %s" % item.query_name)
            else:
                self.print_verbose("add query %s" % item.query_name)
                if (isinstance(self.check_proof, bool) and self.check_proof) or \
                   (isinstance(self.check_proof, str) and item.query_name == self.check_proof):
                    try:
                        if self.print_time:
                            start_time = time.time()
                        os_tactics.check_proof(self.thy, item)
                        if self.print_time:
                            end_time = time.time()
                            elapsed_time = end_time - start_time
                            self.print_verbose(f"{elapsed_time:.2f} seconds")
                    except os_z3wrapper.SMTException as e:
                        # print("--- State ---")
                        # print(e.state)
                        # print("--- pprint map ---")
                        # print(e.state.pprint_map())
                        print("--- Original model ---")
                        print(e.z3_model)
                        model = os_model.convert_model_on_state(
                            self.thy, e.state, e.z3_model, verbose=True, check_model=True)
                        print("--- Converted model ---")
                        print(model.pprint(self.thy))
                        os_model.diagnose_query(self.thy, e.state, model)
                        raise e

            self.thy.add_query(item)
        elif isinstance(item, os_theory.OSAttribDecl):
            if item.attrib_name not in self.thy.attribute_map:
                raise AssertionError("attribute %s not found")
            attrib = self.thy.attribute_map[item.attrib_name]
            if item.operation == "add":
                for th_name in item.th_names:
                    if th_name in attrib:
                        raise AssertionError("add_attrib: theorem %s already has attribute %s" % (
                            th_name, item.attrib_name))
                    attrib.append(th_name)
            elif item.operation == "del":
                for th_name in item.th_names:
                    if th_name not in attrib:
                        raise AssertionError("del_attrib: theorem %s not in attribute %s" % (
                            th_name, item.attrib_name))
                    attrib.remove(th_name)
            else:
                raise AssertionError("unknown attribute operation: %s" % item.operation)
        else:
            raise AssertionError("unknown declaration type: %s" % type(item))

def type_parser(thy: OSTheory, ctxt: VarContext):
    return Lark(os_verify_grammar, start="os_type", parser="lalr",
                transformer=OSVerifyTransformer(thy, ctxt=ctxt))

def term_parser(thy: OSTheory, ctxt: VarContext):
    return Lark(os_verify_grammar, start="os_typed_term", parser="lalr",
                transformer=OSVerifyTransformer(thy, ctxt=ctxt))

def sep_parser(thy: OSTheory, ctxt: VarContext):
    return Lark(os_verify_grammar, start="sep", parser="lalr",
                transformer=OSVerifyTransformer(thy, ctxt=ctxt))

def struct_parser(thy: OSTheory):
    return Lark(os_verify_grammar, start="os_struct_def", parser="lalr",
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

def theory_items_parser(thy: OSTheory, visited: set[str], check_proof: bool,
                        print_time: bool, verbose: bool):
    return Lark(os_verify_grammar, start="os_theory_items", parser="lalr",
                transformer=OSVerifyTransformer(thy, visited=visited, check_proof=check_proof,
                                                print_time=print_time, verbose=verbose))

def parse_type(thy: OSTheory, ctxt: VarContext, s: str) -> OSType:
    return type_parser(thy, ctxt).parse(s)

def parse_term(thy: OSTheory, ctxt: VarContext, s: str) -> OSTerm:
    return term_parser(thy, ctxt).parse(s)

def parse_sep(thy: OSTheory, ctxt: VarContext, s: str) -> os_seplogic.SepConj:
    return sep_parser(thy, ctxt).parse(s)

def parse_struct(thy: OSTheory, s: str) -> os_struct.Struct:
    return struct_parser(thy).parse(s)

def parse_function(thy: OSTheory, s: str) -> os_fixp.OSFunction:
    return function_parser(thy).parse(s)

def parse_predicate(thy: OSTheory, s: str) -> os_fixp.OSFunction:
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

def parse_context(thy: OSTheory, s: str) -> VarContext:
    return context_parser(thy).parse(s)

def parse_imports(thy: OSTheory, s: str) -> os_theory.OSImports:
    return imports_parser(thy).parse(s)

def parse_theory_items(thy: OSTheory, s: str, visited: set[str] = None, *,
                       check_proof: bool = True, print_time: bool = False, verbose: bool = False):
    return theory_items_parser(thy, visited, check_proof, print_time, verbose).parse(s)


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
    # The theory file is located in the osverify/theory folder
    current_file_path = os.path.abspath(__file__)
    current_dirname = os.path.dirname(current_file_path)
    theory_path = os.path.join(current_dirname, "theory/%s.thy" % theory_name)
    with open(theory_path) as f:
        return f.read()


def load_theory_internal(theory_name: str, thy: OSTheory, visited: set[str], *,
                         check_proof=False, print_time=False, verbose=False):
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
    print_time : bool, default to False
        whether to print timing information for each query.
    verbose : bool, default to False
        whether to print debugging information during load

    """
    if theory_name in visited:
        return  # theory already loaded

    visited.add(theory_name)

    if verbose:
        print("read file %s" % theory_name)
    content = read_theory_file(theory_name)
    parse_theory_items(thy, content, visited, check_proof=check_proof,
                       print_time=print_time, verbose=verbose)


def load_theory(theory_name: str, *,
                print_time: bool = False,
                verbose: bool = False,
                check_proof: Union[bool, str] = False) -> OSTheory:
    """Load theory file with the given name.
    
    Parameters
    ----------
    theory_name : str
        name of the theory to be parsed.
    print_time : bool, default to False
        whether to print timing information for each query.
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
                         print_time=print_time, verbose=verbose)
    return thy
