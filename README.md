# OSVAuto
semi-automatic verifier for functional specifications of operating systems

# Installation
In any environment with python and pip, use pip to install Lark: 

```
$ pip3 install Lark
```

# Test Running
Each files with suffix '.thy' in osverify/tests contains either a class of definition of datatype or a specific lemma family with some predicate in it. 
You can edit it by self, or type the following command in the root location to test a file, such as:

```
$ python3 -m unittest osverify.tests.parser_test.OSParserTest.testUcos
```

# Documentation
## Type Definition
Primitive types contains the following type def:
```
$ int x  # int

$ int8u x  # int8u

$ int16u x  # int16u

$ int32u x  # int32u

$ bool x  # boolean

$ consts {  # const def, name is not required here, N_n can be any constant value.
    c_1 = N_1;
    c_2 = N_2;
    ...
    c_n = N_n
  }
```
General types needs to follow the syntax below, ty can be any legal type which already defined:
```
$ ty[] arr  # array type

$ ty<ty,...,ty> b  # bound type, e.g. List<int32u> and Map<int32u, bool>

$ datatype name =  # algebraic type, constructor can be either with parameter or without parameter, amount of constructor must be at least 2
     constr1 | constr2(ty_1 p_1,...,ty_n p_n) | ... | constr_n
 # e.g:
  datatype List<E> =  # recursive algebraic type
    nil
    | cons (E ele, List<E> rest)
   or:
  datatype nat =  # non-recursive algebraic type
    zero
    | succ (nat n)
  
$ struct name {  # struct type
    ty_1 field_name1;
    ty_2 field_name2;
    ...
    ty_n field_namen
  }

$ typedef ty_name = ty  # Assign an alias to a specific type
```
## Term
Array term:
```
$ arr[expr]  # get the ith element of arr, ith can be caculated by expr or be set directly

$ arr[expr := term]  # set the ith element of arr to a specific term
```
Struct term:
```
$ structName { fieldName1 := term1, fieldName2 := term2,..., fieldNameN := termN }  # struct update

$ structName {{ fieldName1 : term1, fieldName2 : term2,..., fieldNameN : termN }}  # struct init
```
Terms constrained by quantifiers
```
$ forall (ty_1 p_1, ..., ty_n p_n) { term }  # classic forall statement

$ forall (p_1 in Gterm) { term }  # declare a local params occurs in a ground term in a forall expr

$ exists (ty_1 p_1, ..., ty_n p_n) { term }  # classic exists statement

$ exists (p_1 in Gterm) { term }  # declare a local params occurs in a ground term in a exists expr
```
let expression
```
$ let let_assign in
    term
  end
  # let_assign is an equation relevants of a variant occurs in term
```
switch expression
```
$ switch (term) {
    case pattern_1 : term_1;
    ...
    case pattern_n : term_n
}
  # pattern_n is a pattern that matches a specific term, term can be any legal term that can be reduced to a specific member with a type,
    the type must matches all of the patterns.
```
if-then-else
```
$ if term {
  term_if
} else {
  term_else
}
```
## Operator
Binary operator contains the following operators:
```
$ &  ^  |  <<  >>   # bit

$ +  -  *  /  # integer

$ <  >  <=  >=  ==  !=  # compare

$ &&  ||  ->  ~  # logic
```
## function
Either keyword 'function' and 'predicate' can be used to declare a recursive or non-recursive function
```
predicate thm_name (ty_1 p_1, ..., ty_n p_n) {
  term
}
```
## Query declarations
```
$ query query_name {
  fixes x : ty_1;
  fixes y : ty_2;
  assumes H1: pred_1;
  assumes H2: pred_2;
  shows pred_3
  proof { tactic }
}
  # use fixes to declare the vars, and assumes to make assumptions, shows to make a conclusion. pred_n is any legal predicate or term.
  # Each assumption can be specified a name such as 'H1'
```
## Tactic
**auto**: invokes the SMT solver on the current proof state, takes an optional list of theorems, which are also given as input to the SMT solver.
```
$ auto

$ auto (theorem)
```
**cases**: correspond to case analysis and induction on an algebraic datatype, respectively. Both tactics are followed by a list of branches with corresponding tactics, 
where each branch either correspond to a constructor of the datatype or is the default branch.
```
$ cases(vptr) {
    case Vptr(eid):
      tactics;;
      ...
    default: ...
```
**simplify**: unfolds any term which can be unfolds indeed, and rewrite some term into simple form

**induction** apply induction on a term that has recursive datatype, x is the var to ind, y and z is to be skolemized by needs:
```
$ induction(x, [y, z])
```
**split_conj**: splits a assumption into serval assumptions:
```
$ split_conj(H1, [H11, H22])
```
There is a ';;' between each tactic command, and a ';' in the end of a proof state of a finished sub-goal like:
```
$ induction(tcbList, [vptr, tcbls]) {
    case nil: auto;
    case cons(tcb, rest):
        cases(vptr) {
            case Vptr(tid):
                simplify;;
                skolemize;;
                split_conj(H2, [H21, H22, H23]);;
                match_show(H23) {
                    1: apply_theorem(TCBNode_P_prioneq_prop_hold, [_, H3, H21]);;
                       auto;
                    2: apply_theorem(IH_rest, [_, H22]);;
                       apply_theorem(map_get_test, [H23, H1]);
                };
            default: auto;
        };
  }
```
