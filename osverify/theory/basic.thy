imports core
imports Map

// Length function
function length<T>(List<T> xs) -> nat {
    switch (xs) {
        case nil: 0;
        case cons(i, xs2): succ(length(xs2));
    }
}

// Append function
function append<T>(List<T> xs, List<T> ys) -> List<T> {
    switch (xs) {
        case nil: ys;
        case cons(i, xs2): cons(i, append(xs2, ys));
    }
}

// Reverse function
function rev<T>(List<T> xs) -> List<T> {
    switch (xs) {
        case nil: nil;
        case cons(i, xs2): append(rev(xs2), cons(i, nil));
    }
}

// Take first n elements of a list
function take<T>(nat n, List<T> xs) -> List<T> {
    switch (n) {
        case zero: nil;
        case succ(n2):
            switch (xs) {
                case nil: nil;
                case cons(x, xs2): cons(x, take(n2, xs2));
            };
    }
}

// Drop first n elements of a list
function drop<T>(nat n, List<T> xs) -> List<T> {
    switch (n) {
        case zero: xs;
        case succ(n2):
            switch (xs) {
                case nil: nil;
                case cons(x, xs2): drop(n2, xs2);
            };
    }
}

// Take segment of a list
function segment<T>(nat m, nat n, List<T> xs) -> List<T> {
    drop(m, take(n, xs))
}

// Membership in a list
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

// Remove value from a list
function list_remove<T>(T x, List<T> xs) -> List<T> {
    switch (xs) {
        case nil: nil;
        case cons(y, xs2):
            if (x == y) {
                list_remove(x, xs2)
            } else {
                cons(y, list_remove(x, xs2))
            };
    }
}

// Maximum values for various word sizes
consts {
    int32u_MAX = 255;
    INT16U_MAX = 65535;
    INT32U_MAX = 4294967295;
}
