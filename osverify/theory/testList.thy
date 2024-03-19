imports basic

query append_nil {
    type T;
    fixes xs: List<T>;
    shows append(nil, xs) == xs
    proof { auto }
}

query append_nil_right {
    type T;
    fixes xs: List<T>;
    shows append(xs, nil) == xs
    proof { induction (xs) {default: auto;} }
}

query append_single {
    type T;
    fixes x : T;
    fixes ys: List<T>;
    shows append(cons(x, nil), ys) == cons(x, ys)
    proof { auto }
}

query append_assoc {
    type T;
    fixes xs: List<T>;
    fixes ys: List<T>;
    fixes zs: List<T>;
    shows append(append(xs, ys), zs) == append(xs, append(ys, zs)) 
    proof { induction (xs) {default: auto;} }
}

query rev_single {
    type T;
    fixes x : T;
    shows rev(cons(x, nil)) == cons(x, nil)
    proof { auto }
}

query rev_append {
    type T;
    fixes xs: List<T>;
    fixes ys: List<T>;
    shows rev(append(xs, ys)) == append(rev(ys), rev(xs))
    proof {
        induction(xs) {
            case nil: auto(append_nil_right<T>);
            case cons(x, xs): auto(append_assoc<T>);
        }
    }
}

query rev_rev {
    type T;
    fixes xs: List<T>;
    shows rev(rev(xs)) == xs
    proof {
        induction(xs) {
            case cons(x, xs): auto(append_single<T>, rev_single<T>, rev_append<T>);
            default: auto;
        }
    }
}
