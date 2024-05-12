# OSVAuto

OSVAuto is a tool designed for verifying functional specifications of operating system kernels. It consists of a language for defining data structures, invariants, and queries (verification conditions). Each query is translated into a form that can be accepted by SMT solvers. If the SMT solver returns a counterexample for a query, the tool attempts to translate it back into the form of the front-end language. We place strong emphasis on making the translation of counterexamples work most of the time, in particular by reducing the use of quantifiers whenever possible.

## Installation

We assume relatively new versions of Python (version 3.12 is suggested). The tool depends on Lark parser and the Z3 prover. Install the dependencies as follows:

```bash
pip install -r requirements.txt
```

## Running tests

Run all unit tests using the following:

```bash
python run_test.py
```

This runs all unit tests located in the folder `osverify/tests`. To run unit tests from a single file, use the appropriate commands beginning with `python -m unittest`. For example, to run all tests in `osverify/tests/term_test.py`, use

```bash
python -m unittest osverify.tests.term_test
```

To run the test case `testParseTerm` in that file, use

```bash
python -m unittest osverify.tests.term_test.OSTermTest.testParseTerm
```

Each file with suffix `.thy` in `osverify/theory` contains OSVAuto theory files. Tests for running single theory files are provided in `parser_test.py`. For example, to run all of the top-level theory files, use

```bash
python -m unittest osverify.tests.parser_test
```

## Language

In this part, we describe the front-end language of OSVAuto.

### Types

The type system of OSVAuto is that of a many-sorted first-order logic with polymorphic types. We support defining new types as structures or algebraic datatypes, and the use of type parameters in the definitions of algebraic datatypes and functions.

#### Primitive types

We support the following primitive types:

* `bool`: boolean values
* `int`: mathematical integers
* `int8u`: unsigned 8-bit integers
* `int16u`: unsigned 16-bit integers
* `int32u`: unsigned 32-bit integers

The last three types are collectively called *bitvector types*, which are used to precisely model the behavior of unsigned integer types in C, including possible overflows. On the other hand, the `int` type is used to model ideal integers, in situations where it is unnecessary to consider possibility of overflow.

#### Array types

For each type `T`, we can form the type of arrays with elements in `T`, written as `T[]`. We follow the convention in Z3, where arrays do not naturally have a size. Instead, constraints on array indices need to be added manually in the specification.

#### Structure types

We allow defining new structures, in a style similar to C. For example, to define a structure `Point` with two `int32u` coordinates `x` and `y`, write:

```c
struct Point {
    int32u x;
    int32u y;
}
```

This defines a new type `Point` that can be used later in the theory.

#### Algebraic datatypes

We also allow defining algebraic datatypes. Each definition of algebraic datatype specifies a list of possible branches. The syntax is close to that in Isabelle.

We illustrate using the definition of addresses and values in the verification of uC/OS-II. Each address is specified by a block number and offset, defined as:

```c
struct addrval {
    int32u block;
    int32u offset;
}
```

Then, each value is either undefined, null value, 32-bit integer or address:

```c
datatype val =
    Vundef | Vnull | Vint32(int32u n) | Vptr(addrval addr)
```

In the definition of an algebraic datatype, it is possible to refer to the type itself. For example, the type of lists can be defined as follows:

```c
datatype List<E> =
    nil | cons (E head, List<E> rest)
```

This example also illustrates the use of type parameters: the definition of list is parameterized over type `E`, for the type of elements in the list. Each list with element of type `E` is either `nil` (the empty list), or a cons cell consisting of first element (type `E`) and the list of remaining elements (type `List<E>`).

After type `List<E>` is declared, we can then form the type of lists with any element type. For example, the type `List<int32u>` is the list of unsigned 32-bit integers, which can be constructed using functions `nil<int32u>` and `cons<int32u>`.

#### Internal types

Several types are supported internally in OSVAuto (e.g. with special syntax and translation procedures). They are declared in `core.thy` and `Map.thy`. In addition to the `List` type introduced above, they are:

* **Products:** given any two types `U` and `V`, we can form their cartesian product `Prod<U, V>`, defined as follows.

  ```c
  datatype Prod<U, V> = pair (U fst, V snd)
  ```

* **Natural numbers:** the type of natural numbers is defined in terms of zero and successors.

  ```c
  datatype nat = zero | succ (nat n)
  ```

* **Options:** option type is used to indicate that some value may be unavailable.

  ```c
  datatype Option<T> = none | some (T val)
  ```

* **Maps:** the map type defines a mapping from keys (of type `K`) to values (of type `V`). They are declared axiomatically, with one axiomatic type and four axiomatic functions.

  ```c
  axiomtype Map<K, V>
  axiomfunc indom<K, V> : K -> Map<K, V> -> bool
  axiomfunc get<K, V> : K -> Map<K, V> -> V
  axiomfunc emptyMap<K, V> : Map<K, V>
  axiomfunc updateMap<K, V> : K -> V -> Map<K, V> -> Map<K, V>
  ```

#### Type definitions

It is possible to define new types as abbreviation of old types. This is usually used to abbreviate instantiation of type parameters. For example, after defining the structure for abstract task control block (`AbsTCB`), we can define `TCBMap` as type abbreviation for the mapping from addresses to abstract task control blocks:

```c
typedef TCBMap = Map<addrval, AbsTCB>;
```

### Expressions

#### Constants

We can declare integer constants in the theory, similar to the use of `#define` in C/C++. For example, the following declares maximum values for the various unsigned integer types.

```c
consts {
    int8u_MAX = 255;
    int16u_MAX = 65535;
    int32u_MAX = 4294967295;
}
```

Then, the terms `int8u_MAX`, etc. can be used anywhere a value of integer or bitvector type is expected. Note these terms do not have a particular integer or bitvector type, instead its exact type is inferred. For example, we can express that an unsigned 32-bit integer is between 0 and 255 as follows:

```
int32u x;
0 <= x <= int8u_MAX
```
Here the type of `int8u_MAX` is inferred to be `int32u`, due to comparison with variable `x` known to have type `int32u`.

#### Array

Array access is given by function call `nth(arr, i)`, with notation `arr[i]`, where both `arr` and `i` can be any expression. Here `arr` has type `T[]` for some type `T`, and `i` has either integer or bitvector type. Then `arr[i]` has type `T`.

Array update is given by function call `Store(arr, i, val)`, with notation `arr[i := val]`. This represents a new array that is equal to `arr`, except at index `i`, where the value is set to `val`.

The above two expressions are usually sufficient for writing the specification. For constructing models, one more function is necessary. The expression `K(x)` denotes an array with default value `x` at every index. Combining `K` and `Store`, we can express any concrete array with non-default value at finite number of indices. For example, to express an array with value 4 at index 1, value 7 at index 3, and 0 everywhere else, we can write:

```
K(0)[1 := 4][3 := 7]
```

#### Structures

For any struct type, we can specify a value of that type by explicitly specifying the value of each field (called structure literals). For example, an `addrval` value with block 1 and offset 4 is written as:

```
addrval{{block: 1, offset: 4}}
```

Another common operation is to update the value of some field in an existing structure. For example, let `addr1` denote the structure above, then the expression

```
addr1{offset: 8}
```

updates the offset of `addr1` to 8, resulting in the structure `addrval{{block: 1, offset: 8}}`.

To access a field of a structure, use the dot notation as in C. For example, `addr1.block` evaluates to 1 and `addr1.offset` evaluates to 4.

The following combines field evaluation and update. The expression

```
addr{offset: addr.offset + 4}
```

increments any address by an offset of 4.

#### Algebraic datatypes

Values of algebraic datatypes are constructed by using one of the constructors as a function (no parenthesis is needed when the number of arguments is zero). For example, the following are concrete values of type `val` (defined above).

```
Vundef
Vnull
Vint32(10)
Vptr(addrval{{block: 1, offset: 4}})
```

As another example, we show how lists can be constructed using `nil` and `cons`:

```
cons(1, cons(2, cons(3, nil)))
```

To ease reading, the above list can also be written (and will be displayed) as `[1, 2, 3]`.

Accessing field of a value of an algebraic datatype uses the same dot notation as for structures. For example, `Vint32(10).n` evalutes to 10, and

```
Vptr(addrval{{block1: 1, offset: 4}}).addr.offset
```

evaluates to 4. Let `ls` be the list `[1, 2, 3]`, then `ls.head` evaluates to 1, `ls.rest.head` evaluates to 2, etc. If a field is evaluated on a branch of algebraic datatype that does not have that field, the result is undefined (usually this means an error in the specification). For example, evaluating `Vint32(10).addr` results in undefined value.

#### Switch expressions

It is common to define the value of an expression based on branch of an algebraic datatype. In OSVAuto, we use the switch-case syntax that is similar to other language such as C. For example, to define the length of a list `xs`, we write:

```
switch (xs) {
    case nil: 0;
    case cons(i, xs2): succ(length(xs2));
}
```

This means if `xs` is in the `nil` branch, then the expression equals 0. If `xs` is in the `cons` branch, bind the two arguments of `cons` to fresh variables `i` and `xs2`, then the value of the expression is (recursively-defined as) `succ(length(xs2))`.

The expression after each `case` is called a *pattern*. There can be more kinds of patterns. One simple notation is the wildcard `_`, as a placeholder for a variable we don't care about. For example, in the above definition the variable `i` is never used. So the pattern `cons(i, xs2)` can be equivalently replaced by `cons(_, xs2)`.

Patterns can also contain structure literals and constants. For example, the following expression returns the block number of a `Vptr` value if the offset is 0, and 0 otherwise.

```
switch (v) {
    case Vptr(addrval{{block: b, offset: 0}}): b;
    default: 0;
}
```

The `default` branch captures all the remaining cases.

#### Quantifiers

In OSVAuto, we allow two kinds of quantifiers: *unrestricted* and *restricted*. The unrestricted quantifiers `forall` and `exists` have the usual meaning in first-order logic. For example, to express the identity for the length of append of two lists, we write:

```
forall (List<T> ls1, List<T> ls2) {
    length(append(ls1, ls2)) == length(ls1) + length(ls2)
}
```

To express that there is always a bigger integer, we write:

```
forall (int x) {
    exists (int y) {
        y > x
    }
}
```

Note that we always require type annotations for the bound variables in quantifiers.

The restricted quantifiers `forall ... in ...` and `exists ... in ...` express quantifying over elements of a list or keys in a map. For example, suppose `xs` has type `List<int32u>`. The following expresses all elements of `xs` is greater than zero.

```
forall (int x in xs) {
    x > 0
}
```

The expression `range(l, u)` where `l` and `u` have type `int32u` expresses the list of integers `x` satisfying `l <= x < u`. A common pattern is to range over indices of an array of fixed size (e.g. 64):

```
forall (int32u i in range(0, 64)) {
    a[i] > 0
}
```

Finally, we can range over keys of a map. Suppose `m` has type `Map<addrval, int32u>`, then the following expresses that all values in the map are greater than zero:

```
forall (addrval k in m) {
    get(k, m) > 0
}
```

The above is equivalent to:

```
forall (addrval k) {
    indom(k, m) -> get(k, m) > 0
}
```

The restricted quantifiers have the nice property that they can always be evaluated on a given model, since there is a finite number of elements/keys in a list/map. This is important for analyzing models and counterexamples from an SMT solver. Hence, we strongly encourage the use of restricted quantifiers whenever possible.

#### Let expressions

Let expressions can be used to simulate local variables. For example, the following expression is equivalent to `(y + z) * (y + z)`.

```
let x = y + z in 
    x * x
end
```

#### If-then-else expressions

If-then-else expressions have syntax similar to C, except we require the else-branch to be written and have the same type as the then-branch. We also require brackets to be written explicitly in both then- and else-branches.

```
if (x > 0) {
  x + 1
} else {
  x + 2
}
```

#### Operators

The following operators are supported in OSVAuto.

Unary operators:

* `!`: logical negation.
* `~`: arithmetic negation (taking the negation of every bit in a bit-vector).

Binary operators:

* `->`: logical implies.
* `&&`: logical and.
* `||`: logical or.
* `==`: equality, defined on *all* types in the natural way.
* `!=`: disequality, also defined on all types and is the negation of equality.
* `<=`, `>=`, `<`, `>`: comparison on integer and bit-vector types.
* `&`, `|`, `>>`, `<<`: arithmetic and, or and shift for 
bit-vector types.

The logical operators `->` and `&&` and `||` has short-circuit evaluation: the second argument is not evaluated when the result is determined by the value of the first argument. For example, writing `indom(k, m) -> get(k, m) > 0` is perfectly fine: if `k` is not in the map `m`, then `indom(k, m)` evaluates to false, and `get(k, m)` will not be evaluated.

### Declarations

Each theory is made up of a list of *declarations*. We describe each of the possible declarations in turn.

#### Defining new types

There are three ways to define new types in OSVAuto, all of which have already been described before:

1. define new structures, using the `struct` keyword.
2. define new algebraic datatypes, using the `datatype` keyword.
3. define type abbreviations, using the `typedef` keyword.

#### Axiomatic declarations

It is also possible to declare new types and terms axiomatically, via `axiomtype` and `axiomfunc` keywords. One example has been given for the `Map` type.

####  Functions and predicates

New functions are defined using either `function` or `predicate` keywords. If the `function` keyword is used, the return type of the function must be specified. If the `predicate` keyword is used, the return type is assumed to be `bool`. Recursive definitions are allowed. Functions and predicates can take type arguments, specified using `<>` brackets after the name of the function. For example, the definition of length of a list is as follows.

```
function length<T>(List<T> xs) -> nat {
    switch (xs) {
        case nil: 0;
        case cons(i, xs2): succ(length(xs2));
    }
}
```

The definition of `inlist` predicate (for whether a given element appears in a list) is as follows.

```
predicate inlist<T>(T x, List<T> xs) {
    switch (xs) {
        case nil: false;
        case cons(y, xs2):
            if (x == y) {
                true
            } else {
                inlist(x, xs2)
            };
    }
}
```

#### Query declarations

Queries express proof obligations in OSVAuto. Each query consists of the following parts:

* Type parameters, keyword `type`.
* Variables, keyword `fixes`.
* Assumptions, keyword `assumes`.
* Conclusion, keyword `shows`.

The following example is a simple theorem about bit-vectors:

```
query zadd_rm_head {
    fixes n: int32u;
    fixes p: int32u;
    fixes q: int32u;
    assumes p == q;
    shows n + p == n + q
    proof { auto }
}
```

The last line `proof { auto }` states that the query can be proved directly by converting to SMT (by an encoding process described in the next section). If a query cannot be solved directly by SMT, tactics can be used to guide the proof. The use of tactics will be described in a later section.

The following gives an example of a query that involves type parameters, and requires induction for its proof.

```
query append_assoc {
    type T;
    fixes xs: List<T>;
    fixes ys: List<T>;
    fixes zs: List<T>;
    shows append(append(xs, ys), zs) == append(xs, append(ys, zs)) 
    proof { induction (xs) {default: auto;} }
}
```

## SMT Encoding

In this section, we describe the process for encoding a proof obligation for the SMT solver.

The first step of encoding is *simplifying* the given term. Simplification reduces let expressions, switch expressions, field access on structure literals and constructors, and expands function definitions using rewrite rules. Here expansion of function definitions and reduction of switch expressions require more explanation, which is given in the next two subsections.

The second step converts each type and term into SMT. The primitive types are converted into corresponding types in SMT. Types defined in OSVAuto (i.e. structures and algebraic datatypes) are converted to declared types in SMT, along with identities that assert the relationship between terms of that type and their fields. Finally, switch statements and (both forms of) quantifiers are converted into if-then-else and quantifier statements in SMT, respectively. These will be explained in more detail, along with correctness proofs, in the following subsections.

### Expansion of function definitions

By default, function definitions are expanded in one of the two situations:

* If the function is non-recursive (does not invoke itself in the function body), application of the function is always expanded.

* If the function is recursive, but the function body consists of a single switch on the branches of one of the input arguments (e.g. `length` and `inlist` above), application of the function is expanded when applied to constructors.

As an example of the second case, the two rewrite rules for `length` are:

```
length(nil) == 0
length(cons(i, xs2)) == succ(length(xs2))
```

(for those familiar with Isabelle, this corresponds to adding `_def` rules for non-recursive functions and `.simps` rules for functions defined by primitive recursion).

It is possible to override the above principles by adding/removing rewrite rules by hand. For example, during the verification uf task-management module of uC/OS-II, after proving several results about `TCBNode_P`, it is desirable to no longer expand its definition for the proof of ensuring queries. Then the expansion of `TCBNode_P` can be disabled by writing:

```
del_attrib rewrite for TCBNode_P_def
```

### Reduction of switch expressions

In OSVAuto, we allow very general kinds of patterns in switch statements. The patterns can include: wildcards, variables, constants, datatype constructors, structure literals, and tuples. Before encoding into SMT, we first reduce the switch expression into a *standard* form, where each case is either a constructor applied to variables or the default case.

The reduction process repeatedly performs one of the following rules to subterms of the expression, until no further rule can be applied. We list the rules along with correctness proofs below.

1. If the first branch is the default case, rewrite the expression into the body of the branch. If the default case appears in the middle (i.e. not as the last branch), remove the following branches.

    Example (for when the default case appears as first branch):

    ```
    switch (x) {
        default: e
        ... other cases ...
    }
    ==>
    e
    ```

    **Proof.** According to the semantics of switch, the branches are matched in order. So the first branch will always be evaluated if it is the default case. Similarly for the case where default appears in the middle.

2. If the first branch is a variable or a wildcard, rewrite the expression into the body of the branch, with the variable replaced by the switched expression. If the variable or wildcard pattern appears in the middle (i.e. not as the last branch), remove the following cases. If the variable or wildcard pattern appears as the last branch, replace by the appropriate default branch.

    Example (for when a variable appears as the first branch):

    ```
    switch (e) {
        case v: e2
        ... other cases ...
    }
    ==>
    e2[e/v]
    ```

    **Proof.** Since a variable or wildcard matches everything, the first branch will always be evaluated, with the variable bound to the switched expression. Similarly for the case where variable or wildcard appears in the middle or as the last branch.

3. If the first branch is a constant `c`, rewrite into the corresponding if-then-else expression, with the else branch containing the other cases.

    Example:

    ```
    switch (e) {
        case c: e2
        ... other cases ...
    }
    ==>
    if (e == c) {
        e2
    } else {
        switch (e) {
            ... other cases ...
        }
    }
    ```

    **Proof.** The first branch matches if the switched expression equals `c` (corresponding to the then-branch). In the case of no match, each of the remaining cases will be matched against the switched expression in order (corresponding to the else-branch).

4. If the first branch is a structure literal with at least one field, rewrite to a switch on the first field of the literal against the first pattern. If the pattern matches, match the original expression against the remaining parts of the structure literal. Otherwise, match the original expression against the remaining branches. If the structure literal has no fields, rewrite to the body of the first case.

    Example:

    ```
    switch (e) {
        case Struct{{field1: pat1, field2: pat2, ...}}:
            expr1;
        ... other cases ...
    }
    ==>
    switch (e.field1) {
        case pat1:
            switch (e) {
                case Struct{{field2: pat2, ...}}:
                    expr1;
                ... other cases ...
            }
        default:
            switch (e) {
                ... other cases ...
            }
    }
    ```

    **Proof.** The first branch matches if all fields in the pattern matches, which is the same as saying the pattern for the first field matches, and the patterns for the remaining fields match. If either of these are not true, the remaining patterns are matched. The rule for the first branch having no fields provides the base-case of this recursive rule.

5. If the switch expression and patterns are products (tuple is a special case of products), match the first part of the product, followed by the second part. If either match fails, match against the remaining branches.

    Example:

    ```
    switch (t1, t2) {
        case (p1, p2): expr1;
        ... other cases ...
    }
    ==>
    switch (t1) {
        case p1:
            switch (t2) {
                case p2: expr1;
                default:
                    switch (t1, t2) {
                        ... other cases ...
                    }
            }
        default:
            switch (t1, t2) {
                ... other cases ...
            }
    }
    ```

    **Proof.** The first branch matches only if the first part of the product matches the first pattern, and the second part of the product matches the second pattern. If either of these are not true, the entire product is matched against the remaining cases.

6. If the branches of the switch are constructors of an algebraic datatype, determine the first branch where the constructor is not applied entirely to variables or wildcards. For the branch, create new variables for each pattern that is not variable or wildcard, and rewrite to first matching on the constructor applied entirely to variables and wildcards, and then matching the tuple of newly-created variables to the corresponding patterns, where the default for each match is the remaining cases.

    Example (where `constr` is a constructor, and `pat` is not variable or wildcard):

    ```
    switch (e) {
        case constr(x, pat): expr1;
        ... other cases ...
    }
    ==>
    switch (e) {
        case constr(x, y):
            switch (y) {
                case pat: expr1;
                default:
                    switch (e):
                        ... other cases ...
            }
        default:
            switch (e):
                ... other cases ...
    }
    ```

    **Proof.** The first branch with patterns that are not variable or wildcard matches when the switched expression `e` does not match any of the earlier patterns, has the constructor given by the branch, and each of the arguments to the constructor matches each of the argument patterns. Argument patterns that are variables or wildcards are always matched. So it remains to match the patterns that are not variables or wildcards, which can be written as matching on a tuple. If the match fails, the expression is matched against the remaining cases.

By performing the above reduction rules repeatedly, we are guaranteed to eventually reach an expression in which any switch expression is in *standard* form. That is, each case is a constructor applied to variables or wildcards, except the last case which can be default. This holds because by the above rules, default branches not appearing last, variable, wildcard, constant, and structure literal branches are always eliminated, and any constructor branches are always rewritten into a form of constructor applied entirely to variable or wildcards.

## Tactics

In this section, we describe the tactic language in OSVAuto.

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
