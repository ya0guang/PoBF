use crate::types;

fn main_tag() {
    let a = types::A::new(1);

    // add taint tag for variable `a`
    // such tagging may be automatically realized in A::new()

    // some operations ...

    // verify that the variable `a` still has the taint tag
}

fn main_tag_not() {
    let a = types::A::new(1);

    // some operations ...

    // verify that the variable `a` doesn't have the taint tag
}

fn tag_prop() {
    let a = types::A::new(1);

    // add taint tag for variable `a`

    // some operations ...

    let b = a.to_b();

    // verify that the variable `b` has the taint tag
    // this may require that the struct propagates all the tags to it's sub-components,
    // and each sub-component propagates all the tags back to it's super-component
}