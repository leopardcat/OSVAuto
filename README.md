# OSVAuto

OSVAuto is a tool designed for verifying functional specifications of operating system kernels. It consists of a language for defining data structures, invariants, and queries (verification conditions). Each query is translated into a form that can be accepted by SMT solvers. If the SMT solver returns a counterexample for a query, the tool attempts to translate it back into the form of the front-end language. We place strong emphasis on making the translation of counterexamples work most of the time, in particular by reducing the use of quantifiers whenever possible.

## Installation

We assume relatively new versions of Python (version 3.12 is suggested). The tool depends on Lark parser and the Z3 prover. Install the dependencies as follows:

```bash
pip install -r requirements.txt
```

## Check a single theory or lemma

To check a theory file, place the file in the `osverify/theory` folder. Then use:

```bash
python -m run --theory <theory_name>
```

To check a single lemma in the theory, use:

```bash
python -m run --theory <theory_name> --lemma <lemma_name>
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

The second step converts each type and term into SMT. The primitive types are converted into corresponding types in SMT. Types defined in OSVAuto (i.e. structures and algebraic datatypes) are converted to declared types in SMT, along with identities that assert the relationship between terms of that type and their fields. Maps and functions on maps are converted into `indom` and `get` functions and predicates on them. Finally, switch statements and (both forms of) quantifiers are converted into if-then-else and quantifier statements in SMT, respectively. These will be explained in more detail, along with correctness proofs, in the following subsections.

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

The above expansion of function definitions are applied to the input proof obligation, the relevant equality theorems are not added into Z3. For example, the rewrite rules of the recursive function `length` is applied only if expressions of the form `length(nil)` and `length(cons(i, xs2))` appears explicitly in the proof obligation. We use the following heuristic for adding equality rules to Z3: for each defined function that appears in the simplified form of the proof obligation, we add the definition of that function with appropriately instantiated type parameters. For example, if `length(xs)` appears in the simplified proof obligation, where `xs` has type `List<int32u>`, then the rewrite rules `length.simps_1<int32u>` and `length.simps_2<int32u>` are added.

### Reduction of switch expressions

In OSVAuto, we allow very general kinds of patterns in switch statements. The patterns can include: wildcards, variables, constants, datatype constructors, structure literals, and tuples. Before encoding into SMT, we first reduce the switch expression into a *standard* form, where each case is either a constructor applied to variables or the default case.

The reduction process repeatedly performs one of the following rules to subterms of the expression, until no further rule can be applied. We list the rules along with correctness proofs below.

1. If the first branch is the default case, rewrite the expression into the body of the branch. If the default case appears in the middle (i.e. not as the last branch), remove the following branches.

    **Example** (for when the default case appears as first branch):

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

    **Example** (for when a variable appears as the first branch):

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

    **Example:**

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

    **Example:**

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

    **Example:**

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

    **Example** (where `constr` is a constructor, and `pat` is not variable or wildcard):

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

### Encoding of structure and algebraic datatypes

We now describe the encoding of structure types and algebraic datatypes. Both are converted into newly declared types in SMT. For datatypes with type parameters, the string form of instantiations of type parameters are added to the type name. For example, the type `List<int32u>` is converted to a newly declared type with name `"List<int32u>"` in Z3. This helps to distinguish between different instantiations of the same datatype.

The following rules add identities characterizing the relations between values of a defined type and their fields.

* For each structure literal, add identity rewriting each field of the literal.

    **Example:** for the expression `addrval{{block: b, offset: o}}`, add the following two identities:

    ```
    addrval{{block: b, offset: o}}.block == b
    addrval{{block: b, offset: o}}.offset == o
    ```

* For each structure update, add identity rewriting each field of the update.

    **Example:** for the expression `v{block := b}`, where `v` has type `addrval`, add the following two identities:

    ```
    v{block := b}.block == b
    v{offset := o}.offset == v.o
    ```

* For each equality (including disequality by negation) between two structures, add an identity rewriting the equality to the conjunction of equality of the fields.

    **Example:** for the expression `v1 == v2`, where `v1` and `v2` has type `addrval`, add the following identity:

    ```
    (v1 == v2) == (v1.block == v2.block && v1.offset == v2.offset)
    ```

* For each expression formed by constructor of a datatype, add identities relating id and field of the expression.

    **Example:** for the expressions `nil` and `cons(x, xs)`, add the following identities:

    ```
    nil.id == 0
    cons(x, xs).id == 1
    cons(x, xs).head == x
    cons(x, xs).rest == xs
    ```

    Note the id's are given as integers starting from 0. For each constructor, only identities for those fields that are present are added (e.g. there is no identity for `nil.head`).

* For each equality (including disequality by negation) between two datatype values, add identity rewriting the equality to equalities between fields conditioned by id.

    In the most general case where neither side of equality is in constructor form (so which branch of the datatype the two sides are on is a priori unknown), each possible case of id need to be considered.

    For datatype that are inductive (i.e. the type itself appears in one of the branches), it is crucial that equalities on the same type in the created identities are not rewritten. This prevents the infinite loop produced by inductive datatypes.

    **Example:** for the expression `xs1 == xs2`, where the two sides have type `List<int32u>`, add the following identity:

    ```
    (xs1 == xs2) == (
        xs1.id == xs2.id &&
        (xs1.id == 0 -> true) &&
        (xs1.id == 1 -> xs1.head == x2.head && x1.rest == x2.rest)
    )
    ```

    Here the equality `x1.rest == x2.rest` are not further expanded to prevent the infinite loop.

* For each (instantiation of type parameters of) algebraic datatype, add inequalities specifying the range of id. In this case, forall-quantification is used, as there is no danger of infinite loops resulting from instantiation.

    **Example:** if the type `List<int32u>` appears in the goal, then the following inequalities are added:
    
    ```
    forall (List<int32u> xs) { xs.id >= 0 && xs.id < 2 }
    ```

Note the above identities are still written in the original language of OSVAuto. To fully convert into Z3 terms, each field access (including `.id`) is converted into application of uninterpreted functions (with names containing instantiation of type parameters). For example, in the case of `xs` with type `List<int32u>`, `xs.id` is converted into `id<int32u>(xs)`, `xs.head` and `xs.rest` are converted into `head<int32u>(xs)` and `rest<int32u>(xs)`, respectively. The constructors `nil` and `cons` are converted into uninterpreted functions `nil<int32u>` and `cons<int32u>` as well.

**Proof of correctness:** the above identities express the interpretation of structure types and algebraic datatypes: each value of structure type is characterized precisely by the values of its fields, and each value of algebraic datatype is characterized precisely by the index of branches and the values of fields of that index.

The above argument shows the encoding is *sound* but does not mean it is *complete*. In fact because the encoding of equalities do not extend to those recursively generated for inductive datatypes, the encoding is not complete. Decision procedures for (inductive) datatypes are a well-researched problem. More work is needed to add more general (but hopefully still reliably efficient) algorithms to the tool.

### Encoding of maps

As explained in an earlier section, each map type `Map<K,V>` is encoded with two uninterpreted functions `indom<K,V>` and `get<K,V>`. Each function/predicate on maps are expanded into their definitions in terms of `indom` and `get`. The following predicates are currently supported:

* `isEmpty(m)`: whether a map `m` is empty.
* `subseteq(m1, m2)`: the domain of `m1` is a subset of the domain of `m2`, and the values of `m1` and `m2` are equal on the domain of `m1`.
* `join(k, v, map_ori, map_new)`: the key `k` is not present in `map_ori`, and adding the key-value pair `(k, v)` to `map_ori` results in `map_new`.
* `mapUpdate(k, v, map_ori, map_new)`: the key `k` may or may not be present in `map_ori`, but adding/updating the key-value pair `(k, v)` to `map_ori` results in `map_new`.
* `sigJoin(k, v, sig_map)`: the map `sig_map` consists of a single key-value pair `(k, v)`.
* `remove(k, map_ori, map_new)`: the key `k` is present in `map_ori`, and removing `k` from `map_ori` results in `map_new`.
* `mapEq(m1, m2)`: the equality relation on maps, `m1` and `m2` have the same set of keys and have the same value for each key.
* `disjoint(m1, m2)`: the sets of keys of `m1` and `m2` are disjoint.
* `merge(m1, m2, m_new)`: the set of keys in `m_new` is the union of sets of keys of `m1` and `m2`, and for each key in each of `m1` and `m2`, the corresponding value in `m1` and `m2` agrees with that in `m_new`. Note this does not require the set of keys in `m1` and `m2` to be disjoint, but the values should agree for each key in the intersection.
* `minus(m1, m2, m_new)`: the set of keys in `m_new` is the set of keys of `m1` minus the set of keys of `m2`, and for each key in `m_new`, the corresponding value in `m_new` equals that in `m1`.

For each predicate, application of the predicate is expanded into a logical formula in terms of `indom` and `get` *only during SMT encoding*. This keeps the expressions succinct for the user. We give some representative examples for the expansion below.

* Expansion of `mapEq`:

    ```
    predicate mapEq<K, V>(Map<K, V> m1, Map<K, V> m2) {
        forall (K k) {
            indom(k, m1) == indom(k, m2) && 
            (indom(k, m1) -> get(k, m1) == get(k, m2))
        }
    }
    ```

* Expansion of `join`:

    ```
    predicate join<K, V>(K key, V value, Map<K, V> map_ori, Map<K, V> map_new) {
        !indom(key, map_ori) && indom(key, map_new) && get(key, map_new) == value &&
        forall (K k) {
            k != key -> indom(k, map_ori) == indom(k, map_new) &&
                        (indom(k, map_ori) -> get(k, map_ori) == get(k, map_new))
        }
    }
    ```

* Expansion of `mapUpdate`:

    ```
    predicate mapUpdate<K, V>(K key, V value, Map<K,V> map_ori, Map<K, V> map_new) {
        indom(key, map_new) && get(key, map_new) == value &&
        forall (K k) {
            k != key -> indom(k, map_ori) == indom(k, map_new) &&
                        (indom(k, map_ori) -> get(k, map_ori) == get(k, map_new))
        }
    }
    ```

**Proof of correctness:** we simply check that the expansion of each predicate correctly expresses the meaning of the predicate. For example, the expansion for `join` asserts that:

* the input key is not in the original map,
* the input key is in the new map,
* the value for the input key is correct in the new map,
* and every key other than the input key is present in the new map if and only if it is present in the old map, and the corresponding values are equal if present.

The expansion of `mapUpdate` is the same as `join`, except there is no requirement on the input key not in the original map. The expansion of `mapEq` asserts that the set of keys are the same, and the corresponding values are equal for each key that is present.

### Encoding of switch statements

For switch statements, we assume that the previous simplification step has already put it in standard form. That is, the switched expression must be an algebraic datatype, and each case is a constructor applied to variables or wildcards, except for the last case which may be default.

A switch expression in standard form is converted into a series of if-then-else statements, depending on the id of the switched expression. For example, the following switched expression on `xs` of type `List<int32u>`:

```
switch (xs) {
    case nil: expr1
    case cons(x, xs2): expr2
}
```

is first written in an intermediate form:

```
if (xs.id == 0) {
    expr1
} else {
    expr2[xs.head/x, xs.rest/xs2]
}
```

where the expression in the else-branch means substituting `xs.head` for each appearance of `x` and `xs.rest` for each appearance of `xs2` in `expr2`. This intermediate form is then converted into Z3 by replacing e.g. `xs.id` by `id<int32u>(xs)`, `xs.head` by `head<int32u>(xs)` and `xs.rest` by `rest<int32u>(xs)`.

**Proof of correctness:** for a switch expression in standard form, each case covers exactly one of the branches of the datatype (except possibly for the last default case, which may cover several branches). The fact that a value of algebraic datatype is in one of the branches is equivalent to the id of the value equal to the corresponding integer. Hence it is logically equivalent to convert each case of the switch to an if-expression. The then-branch of the if-expression is the substituted form of the body of the case, in accordance with the interpretation of variables in the pattern, which are bound to the appropriate field of the switched expression in the body.

One important property of the above encoding is that no quantifiers are introduced in the process. Hence, the encoded Z3 goal is quantifier-free if the original goal is, which is advantageous for SMT solvers since they often do not handle quantifiers very well.

### Encoding of quantifiers and existing theorems

If the original goal does have quantifiers, they must be encoded as quantifiers in SMT goals as well. The encoding for unrestricted quantifiers is straightforward. The encoding for restricted quantifiers expands its meaning into unrestricted quantifiers. The following gives the various cases.

* Forall quantification restricted to map:

    ```
    forall (K key in map) {
        body
    }
    ==>
    forall (K key) {
        indom(key, map) -> body
    }
    ```

* Exists quantification restricted to map:

    ```
    exists (K key in map) {
        body
    }
    ==> 
    exists (K key) {
        indom(key, map) && body
    }
    ```

* Forall quantification restricted to list:

    ```
    forall (T x in list) {
        body
    }
    ==>
    forall (T x) {
        inlist(x, list) -> body
    }
    ```

* Exists quantification restricted to list:

    ```
    exists (T x in list) {
        body
    }
    ==>
    exists (T x) {
        inlist(x, list) && body
    }
    ```

* Forall quantification restricted to range:

    ```
    forall (int32u i in range(l, u)) {
        body
    }
    ==>
    forall (int32u i) {
        l <= i && i < u -> body
    }
    ```

* Exists quantification restricted to range:

    ```
    exists (int32u i in range(l, u)) {
        body
    }
    ==>
    exists (int32u i) {
        l <= i && i < u && body
    }
    ```

**Proof of correctness:** by the interpretation of restricted quantification, and interpretation of `range` function.

## Model reconstruction

An important functionality supported by OSVAuto is to provide understandable counterexamples to the user if the SMT solver fails to prove the goal. As long as we are careful in keeping the quantifiers under control, most of the time Z3 will either proof the goal or return a counterexample. However, the counterexample returned by Z3 consists of instantiation of the variables and functions in the encoding, which is a bit far-removed from the original language of OSVAuto. Hence, it is necessary to "undo the encoding" in transforming the counterexample produced by Z3 back into a model in the language of OSVAuto.

The eventual model in OSVAuto should map each variable in the original proof obligation to *fully-evaluated expressions*. These expressions are in one of the following forms:

* Boolean and integer constants.
* Arrays and maps, where each element in the array, or every key and value in the map are fully-evaluated.
* Structure literals, where the value of each field is fully-evaluated.
* Applications of constructor of a datatype, where each argument of the constructor is fully-evaluated.
* Unknown values (written as `?`), for the case where the validity of the counterexample does not depend on those values.

A simple example of unknown values is as follows. Suppose a structure `struct Point { int32u x; int32u y }` is defined, and the goal to be proved is `x > 0`. Then the returned counterexample may be `Point {{ x: 0; y: ? }}`.

The main work that are necessary to undo the encoding is to interpret the instantiations of new functions produced by the encoding, these include:

* For structures and datatypes, functions for `id` and each `field`. This includes the case of datatype `List`.
* For arrays, the functions `K` and `Store`.
* For maps, the functions `indom` and `get`.

Next, we give more details about SMT counterexamples that are specific to Z3, which are assumed in all of the following subsections.

* For each declared sort (such as translated sort of structures and datatypes), each value of that sort has the form `{sortName}!val!{index}`. For example, values of datatype `addrval` in the counterexample produced by Z3 has names `addrval!val!0`, `addrval!val!1`, and so on. Note if the type has parameters, the type name include instantiations of the parameters. For example, values of `List<int32u>` in the Z3 counterexample has names `List<int32u>!val!0`, etc.

    An implication for this convention is that by scanning through a Z3 expression, we can collect values of each declared type appearing in the expression. We do this for each expression in the Z3 model, and use this information in the decoding of maps.

* For each declared (uninterpreted) function, such as the `indom` and `map` functions produced by encoding of maps, the value produced by Z3 is a finite representation of a function. This function usually has the following form: a pair of key-value pairs that give values for certain inputs, followed by an *else* branch that give the default value, or further evaluation rules depending on the input parameters. Usually, we don't need to be concerned about exact representation of functions, as the Z3 provides an API for evaluating the function on concrete inputs.

### Reconstruction for structures

For a structure value, we look for functions corresponding to each field of the structure, and evaluate the Z3 function on the Z3 value. As an example, consider the following test case: the theory is extended by structure definition for `Point`:

```
struct Point {
    int32u x;
    int32u y;
}
```

and the query is:

```
query testStructPoint {
    fixes p: Point;
    fixes q: Point;
    assumes p.x == 2 && p.y == 3 && q.x == 4 && q.y == 5
}
```

The model returned by Z3 is as follows:

```
[p = Point!val!0,
 q = Point!val!1,
 Point.y = [Point!val!1 -> 5, else -> 3],
 Point.x = [Point!val!1 -> 4, else -> 2]]
```

This means `p` and `q` are values of declared sort `Point` with index 0 and 1 respectively. The fields `x` and `y` of `Point` are represented as functions mapping `Point` values to values of its fields. Reconstruction from this model proceeds by the following steps:

1. For point `p` with Z3 value `Point!val!0`, evaluate functions `Point.x` and `Point.y` on `Point!val!0`, yielding 2 and 3 respectively. So point `p` has value `Point{{x: 2, y: 3}}`.

2. For point `q` with Z3 value `Point!val!1`, evaluate functions `Point.x` and `Point.y` on `Point!val!1`, yielding 4 and 5 respectively. So point `q` has value `Point{{x: 4, y: 5}}`.

### Reconstruction for datatypes

Reconstruction for datatypes differs from that for structures only in the need to evaluate `id`. For each datatype value, first the Z3 function for `id` is evaluated, giving which branch of the datatype the value is on. Then each field of that branch is evaluated. Again, we give a concrete example as follows.

Suppose the theory is extended by datatype definition for `Point`:

```
datatype Point =
    PointA(int32u x, int32u y) | PointB (int32u x, int32u z)
```

and the query is:

```
query testDatatype {
    fixes v: Point;
    fixes w: Point;
    assumes v == PointA(2, 3) && w == PointB(4, 5)
}
```

The model returned by Z3 is as follows:

```
[w = Point!val!1,
 v = Point!val!0,
 Point.id = [Point!val!0 -> 0, else -> 1],
 Point.z = [else -> 5],
 Point.y = [else -> 3],
 PointB = [else -> Point!val!1],
 PointA = [else -> Point!val!0],
 Point.x = [Point!val!1 -> 4, else -> 2]]
```

This means `v` and `w` are values of declared sort `Point` with index 0 and 1, respectively. The fields `x`, `y` and `z` are represented as functions mapping `Point` values to values of its fields. The `id` of each `Point` value are given by the Z3 function `Point.id`. Reconstruction from this model proceeds by the following steps:

1. For point `v` with Z3 value `Point!val!0`, first evaluate `Point.id` on `Point!val!0`, yielding value 0. This means `v` is on the branch `PointA`, with fields `x` and `y`. Then evaluate functions `Point.x` and `Point.y` on `Point!val!0`, yielding values 2 and 3 respectively. So point `v` has value `PointA(2, 3)`.

2. For point `w` with Z3 value `Point!val!1`, first evaluate `Point.id` on `Point!val!1`, yielding value 1. This means `w` is on the branch `PointB`, with fields `x` and `z`. Then evaluate functions `Point.x` and `Point.z` on `Point!val!1`, yielding values 4 and 5 respectively. So point `w` has value `PointB(4, 5)`.

We give one more example illustrating reconstruction for a datatype with recursion and type parameters. The test query is:

```
query testDatatype {
    fixes xs : List<int32u>;
    assumes xs == [1, 2]
}
```

The model returned by Z3 has the following form (the complicated value for `List.id` is omitted).

```
[xs = List<int32u>!val!2,
 nil<int32u> = List<int32u>!val!0,
 v = List<int32u>!val!3,
 List.id<int32u> = [...],
 List.rest<int32u> = [List<int32u>!val!1 ->
                      List<int32u>!val!0,
                      else -> List<int32u>!val!1],
 List.ele<int32u> = [List<int32u>!val!2 -> 1, else -> 2],
 cons<int32u> = [(1, List<int32u>!val!1) ->
                 List<int32u>!val!2,
                 else -> List<int32u>!val!1]]
```

Reconstruction of this model proceeds as follows.

1. The only variable is `xs`, with Z3 value `List<int32u>!val!2`. First evaluate `List.id<int32u>` on `List<int32u>!val!2`, which yields 1. So `xs` is on the cons branch. Then evaluate `List.ele<int32u>` and `List.rest<int32u>` on `List<int32u>!val!2`, yielding 1 and `List<int32u>!val!1` respectively. This means `xs` has form `cons(1, xs2)` where `xs2` has Z3 value `List<int32u>!val!1`.

2. Next, evaluate `List.id<int32u>` on `List<int32u>!val!1`, which yields 1. So `xs2` is on the cons branch. Then evaluate `List.ele<int32u>` and `List.rest<int32u>` on `List<int32u>!val!1`, yielding 2 and `List<int32u>!val!0` respectively. This means `xs2` has form `cons(2, xs3)` where `xs3` has Z3 value `List<int32u>!val!0`.

3. Finally, evaluate `List.id<int32u>` on `List<int32u>!val!0`, which yields 0. This means `xs3` is nil, which completes the reconstruction, giving `xs` having value `cons(1, cons(2, nil))`, or `[1, 2]` using syntax sugar.

### Reconstruction for arrays

The model for arrays is already in evaluated form, consisting of `K` and `Store` functions. For example, with the following test query:

```
query testArray {
    fixes a : int32u[];
    fixes x : int32u;
    fixes y : int32u;
    assumes x == 0 && y == 1;
    assumes a[x] == 1 && a[y] == 3
}
```

the model returned by Z3 is:

```
[y = 1, x = 0, a = Store(K(Int, 3), 0, 1)]
```

This means `a` is an array with value 3 everywhere, except the value at index 0 is updated to 1. The corresponding value in OSVAuto is `Store(K(3), 0, 1)`, or `K(3)[0 := 1]` using syntax sugar.

### Reconstruction for maps

The main work that need to be done to reconstruct models for maps is to evaluate the corresponding indom and get functions. One difficulty is to obtain the list of potential keys. For this purpose, we scan through the Z3 expression for each function, looking for values of declared sorts as well as of primitive types in the expression.

First consider an example where the keys are of primitive type. The test query is:

```
query testMap {
    fixes x: int32u;
    fixes y: int32u;
    fixes z: int32u;
    fixes m: Map<int32u, int32u>;
    assumes indom(x, m) && indom(y, m) && indom(z, m);
    assumes get(x, m) == 1 && get(y, m) == 2 && get(z, m) == 3
}
```

The model returned by Z3 is:

```
[m = Map<int32u,int32u>!val!0,
 y = 1,
 x = 2,
 z = 0,
 indom<int32u,int32u> = [else -> True],
 get<int32u,int32u> = [(1, Map<int32u,int32u>!val!0) -> 2,
                       (0, Map<int32u,int32u>!val!0) -> 3,
                       else -> 1]]
```

First, we go through each Z3 expression in the model, collecting atomic subexpressions of type int32u. These are 0, 1, and 2. Then, for variable `m` with Z3 value `Map<int32u,int32u>!val!0`, first evaluate `indom` on each of 0, 1, and 2, which yields true for all three values. Then, evaluate `get` on each of 0, 1, and 2, which yields 3, 2, 1 respectively. So the model for `m` is `{0: 3, 1: 2, 2: 1}`.

For this example, Z3 chooses to return an `indom` that is true on all keys. However, we don't care about keys not present in the model, and still return a finite map with keys containing all `int32u` values appearing in the model.

Finally, we consider an example where keys to the map are defined types. Again extend the theory with structure `Point`. The test query is:

```
query testMap2 {
    fixes p: Point;
    fixes q: Point;
    fixes m: Map<Point, int32u>;
    assumes p == Point {{x: 0, y: 1}};
    assumes q == Point {{x: 2, y: 3}};
    assumes indom(p, m) && get(p, m) == 0;
    assumes indom(q, m) && get(q, m) == 1
}
```

The Z3 model is (with some irrelevant values omitted):

```
m = Map<Point,int32u>!val!0
p = Point!val!0
q = Point!val!1
get<Point,int32u> = [
    (Point!val!1, Map<Point,int32u>!val!0) -> 1,
    else -> 0]
indom<Point,int32u> = [else -> True]
Point.y = [Point!val!1 -> 3, else -> 1]
Point.x = [Point!val!1 -> 2, else -> 0]
```

First, we collect atomic values of type `Point` among the Z3 model, yielding `Point!val!0` and `Point!val!1`. Evaluating `indom` on these two values and value for `m`, we found both appear as keys in the map `m`. Then evaluate `get` on these two values and value for `m`, yielding the value for `Point!val!0` is 0 and value for `Point!val!1` is 1. Further evaluating `Point!val!0` and `Point!val!1` (according the rules for evaluating structures), we found they have value `Point{{x: 0, y: 1}}` and `Point{{x: 2, y: 3}}` respectively. So the full model for `m` is:

```
{
    Point{{x: 2, y: 3}}: 1,
    Point{{x: 0, y: 1}}: 0,
}
```

## Tactics

While the use of SMT solvers substantially increases the level of proof automation, there are still some proof obligations that is outside the capability of current SMT solvers. In particular, we cannot expect SMT solvers to perform inductive proofs, and they can easily be confused by a large number of quantified facts. Hence, we still allow the user to guide the proof using a tactic language. The tactic language in OSVAuto is in part inspired by that in Coq and Isabelle, but we also make changes so it fits better with stronger proof automation (and hence short manual proofs in general), and to avoid some of the problems encountered in existing proof assistants.

### Proof states

Before introducing tactics, we first discuss the concept of *proof states* in OSVAuto. In contrast to the notion of proof states in most other proof assistants, where a proof state simply consists of the current list of assumptions and goal, a proof state in OSVAuto maintains information about all current subgoals together with branching information. (A more appropriate analogy is to the list of currently open subgoals in Coq or Isabelle, but with additional branching information.)

The list of possible types of proof states is as follows. In the implementation, the base class of proof states is `AbstractProofState`. The class for each type of proof state extends `AbstractProofState`, with the class name given in parenthesis.

* Empty state (`EmptyProofState`): indicates a proof state that has already been resolved (e.g. there are zero subgoals remaining).

* Case branching (`CaseProofState`): indicates a proof state resulting from applying case analysis or induction on an algebraic datatype. It consists of one branch for each constructor of the datatype, with name of the constructor and list of variables for the argument of the constructor. These variables are newly introduced and the proof state of the branch as its scope.

* Indexed branching (`IndexProofState`): indicates a proof state resulting from applying some tactic that results in a number of subgoals. It consists of a number of proof states indexed by integers starting from 1. Each proof state corresponds to a subgoal generated by the tactic.

* Assertion branching (`AssertProofState`): indicates a proof state resulting from applying the assert tactic, or another tactic that first asserts some proposition to be true, then uses that proposition to transform the goal. It consists of two branches: the `assert_case` for proving the asserted proposition, and the `remain_case` for proving the resulting subgoal.

* Basic state (`ProofState`): this is the most basic kind of proof state, with the same components as a query (except it has no name): type parameters, variables, assumptions, and conclusion.

Initially, a basic state is created from a query. Then, tactics are applied to the proof state, until all leaves in the tree of proof states are empty states. On the other hand, the number of leaves that are basic state is the number of remaining subgoals in the proof.

### List of tactics

We now discuss each of the tactics that we currently support. An overview table is as follows.

| Tactic | Description |
| ------ | ----------- |
| Skip   | do nothing |
| Then   | apply two tactics in sequence |
| ThenSplit | apply one tactic, followed by tactics for each case |
| Auto   | use SMT solver to solve goal |
| Simplify | simplify the current proof state |
| Exists | provide witness for existence goal by hand |
| Skolemize | create fresh variables from existence fact |
| Assert | assert proposition, then add it to assumption |
| Change | assert equality, then use it to rewrite goal |
| Assumption | use one of the assumptions to solve goal |
| SplitConj | split conjunction in goal |
| MatchShow | match existential goal statement with assumption |
| ApplyTheorem | apply existing theorem or fact |
| Cases  | apply case analysis |
| Induction | apply induction |

Next, we describe each of the tactics in detail, including syntax in the tactic language, possible parameters, and so on.

#### Skip

* Syntax: `skip`
* Leave the current proof state unchanged, usually used as a placeholder for when a tactic is needed but it is unclear what to do.

#### Then

* Syntax: `tac1 ;; tac2`
* First perform `tac1`, then perform `tac2`. The tactic `tac1` *must* result in a basic proof state (no branching), otherwise an exception is raised.

#### ThenSplit

* Syntax: `tac { 1: tac1; 2: tac2; ... }`
* First perform `tac`. It must create an indexed proof state (otherwise an exception is raised). Then apply `tac1`, `tac2`, etc to each indexed branch. It is also possible to use `default: tac'` to apply `tac'` to all remaining branches.

#### Auto

* Syntax: `auto` or `auto(thm_specs)`
* Apply SMT solver. The auto tactic optionally takes a list of theorem names as argument. If the theorem has type parameters, instantiations of type parameters *must* be provided. For example, to add the simplification rules for `inlist` with type argument `int32u`, use:

    ```
    auto(inlist_simps1<int32u>, inlist_simps2<int32u>)
    ```

    If SMT solver successfully solves the goal, the proof state is transformed into empty state. Otherwise an exception is raised, together with possible counterexample given by the SMT solver. (It is not possible for `auto` to be partially applied, leaving an intermediate proof state).

#### Simplify

* Syntax: `simplify`
* Apply simplification to all assumptions and conclusion in the proof state. This is the same simplification that is performed before SMT encoding.

#### Exists

* Syntax: `exists(args)`
* Provide witness for existence goal by hand. The list of arguments `args` is a comma-separated list of expressions, which must equal the number of exists quantifiers in the current subgoal.

#### Skolemize

* Syntax: `skolemize(name, [vars])`
* Create fresh variable from an existence fact. The argument `name` provides name of the fact (which must be named for this tactic to be used). The list of variables `vars` is a comma separated list of `type var_name` declarations. For example, given existence fact

    ```
    H1: exists (int32u x, int32u y) { x + y > 0 }
    ```

    Using the tactic `skolemize(H1, [int32u x0, int32u y0])`, we transform the proof state into:

    ```
    fixes x0 : int32u
    fixes y0 : int32u
    H1: x0 + y0 > 0
    ```

#### Assert

* Syntax: `assert (name: prop) { tac1 };; tac2`
* Assert the given proposition `prop`, use tactic `tac1` to prove the proposition, then apply tactic `tac2` on the proof state obtained by adding `prop` as one of the assumptions with given the `name`. This tactic transforms a basic proof state into an assertion branching.

#### Change

* Syntax: `change (prop) { tac1 };; tac2`
* Assert the given equality proposition `prop`, use tactic `tac1` to prove the equality, then apply tactic `tac2` on the proof state obtained by applying the equality to rewrite the current proof state. This tactic transforms a basic proof state into an assertion branching.

#### Assumption

* Syntax: `assumption`
* Try to find current goal in the list of assumptions. If it is found, change the proof state into empty state. Otherwise raise an exception.

#### SplitConj

* Syntax: `split_conj(name, [names])`
* Split the conjunction in the given assumption. The name of the original assumption is given as `name`. The name of new assumptions are given in the list `names`, whose length must match the number of conjuncts in the original assumption.

#### MatchShow

* Syntax:

    1. `match_show(name);; tac` or
    2. `match_show(name) {1: tac1; 2: tac2; ...}`

* Match existential goal statement with the given assumption. The goal must be in the form `exists (v_1, ..., v_n) {Q_1 && ... && Q_k}`. Match one of the patterns `Q_i` with the named assumption in order to instantiate the variables `v_1, ..., v_n`. The remaining conjuncts of the goal are instantiated and left as subgoals.

    If the tactic results in a single subgoal, the first version of syntax is used. If it results in more than one subgoal, the second version is used.

#### ApplyTheorem

* Syntax:

    1. `apply_theorem(name, [facts]);; tac` or
    2. `apply_theorem(name, [facts]);; {1: tac1; 2: tac2; ...}`

* Apply theorem with the given name, or assumption with given label on the current proof state. The optional list of facts provides additionally instantiations for the assumptions of the theorem in order. If no fact is available for one of the assumptions, the wildcard `_` can be used as placeholder.

    If the tactic results in a single subgoal, the first version of syntax is used. If it results in more than one subgoal, the second version is used.

#### Casees

* Syntax:

```
cases(e) {
    case constr1: tac1;
    case constr2: tac2;
    ...
}
```

* Apply case analysis on an expression `e` whose type is an algebraic datatype. Following `cases` is a list of branches, one for each constructor of the datatype. Each branch is specified by the constructor name, possible list of variable arguments, and tactic used to solve that branch. It is also possible to use `default: tac'` to apply `tac'` to all remaining branches.

#### Induction

* Syntax:

```
induction(e, [arbitraries]) {
    case constr1: tac1;
    case constr2: tac2;
    ...
}
```

* Apply induction on an expression `e` whose type is an algebraic datatype. Following `induction` is a list of branches, one for each constructor of the datatype. Each branch is the same as that for tactic `cases`, except an addition induction hypothesis is available. The naming convention for each induction hypothesis is `IH_{var_name}`, where `var_name` is the name of the variable argument which created the induction hypothesis.

    Moreover, an optional list of arbitrary variables may be specified after the expression to be inducted upon. These variables will be for-all quantified to create the statement to be proved by induction.

### Examples

We use some examples of theorems about lists to illustrate our tactic language.

We assume that standard functions on lists `append` and `rev` has already been defined. For the query:

```
query append_nil_right {
    type T;
    fixes xs: List<T>;
    shows append(xs, nil) == xs
}
```

It suffices to perform induction on variable `xs`, then the rest can be handled by an SMT solver. So the proof is:

```
proof { induction (xs) {default: auto;} }
```

Likewise, the following query, stating associativity of list append, is proved similarly.

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

Now we come to the interesting parts. For the query about relation between `rev` and `append`:

```
query rev_append {
    type T;
    fixes xs: List<T>;
    fixes ys: List<T>;
    shows rev(append(xs, ys)) == append(rev(ys), rev(xs))
}
```

Suppose we know the first step is to perform induction on `xs`, but don't know what to do afterwards, we can preliminarily write the proof as:

```
proof {
    induction(xs) {
        case nil: skip;
        case cons(x, xs): skip;
    }
}
```

Running OSVAuto, the tool will indicate that two subgoals are remaining, together with an hierarchical display of the subgoals:

```
nil {
  type T
  fix ys: List<T>
  prove rev(append([], ys)) == append(rev(ys), rev([]))
}
cons(x, xs) {
  type T
  fix ys: List<T>
  fix x: T
  fix xs: List<T>
  assume IH_xs: rev(append(xs, ys)) == append(rev(ys), rev(xs))
  prove rev(append(cons(x, xs), ys)) == append(rev(ys), rev(cons(x, xs)))
}
```

It indicates that the first subgoal corresponds to the nil case, and the second subgoal for the cons case, with `x` and `xs` as the fresh variables. The nil case can be proved by adding theorem `append_nil_right` instantiated to type `T`. The cons case can be proved by adding theorem `append_assoc` instantiated to type `T`. Hence, the full proof is:

```
proof {
    induction(xs) {
        case nil: auto(append_nil_right<T>);
        case cons(x, xs): auto(append_assoc<T>);
    }
}
```

Finally, to show that reversing a list twice yields the original list:

```
query rev_rev {
    type T;
    fixes xs: List<T>;
    shows rev(rev(xs)) == xs
}
```

It is known that induction on `xs` should be used, and the theorem `rev_append` should be used in the cons case. The remaining case (for nil) can be proved by SMT directly. So the proof can be written as:

```
proof {
    induction(xs) {
        case cons(x, xs): auto(rev_append<T>);
        default: auto;
    }
}
```
