imports basic

query append_nil_right {
    type T;
    fixes xs: List<T>;
    shows append(xs, nil) == xs
    proof { induction (xs) {default: auto;} }
}

query append_assoc {
    type T;
    fixes xs: List<T>;
    fixes ys: List<T>;
    fixes zs: List<T>;
    shows append(append(xs, ys), zs) == append(xs, append(ys, zs)) 
    proof { induction (xs) {default: auto;} }
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
            case cons(x, xs): auto(rev_append<T>);
            default: auto;
        }
    }
}
