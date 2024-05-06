imports basic

query append_nil_right {
    fixes xs: List<int32u>;
    shows append(xs, nil) == xs
    proof { induction (xs) {default: auto;} }
}

query append_assoc {
    fixes xs: List<int32u>;
    fixes ys: List<int32u>;
    fixes zs: List<int32u>;
    shows append(append(xs, ys), zs) == append(xs, append(ys, zs))
    proof { induction(xs) {default: auto;} }
}

query rev_append {
    fixes xs: List<int32u>;
    fixes ys: List<int32u>;
    shows rev(append(xs, ys)) == append(rev(ys), rev(xs))
    proof {
        induction(xs) {
            case nil: auto(append_nil_right);
            case cons(x, xs): auto(append_assoc);
        }
    }
}

query rev_rev {
    fixes xs: List<int32u>;
    shows rev(rev(xs)) == xs
    proof {
        induction(xs) {
            case cons(x, xs): auto(rev_append);
            default: auto;
        }
    }
}
