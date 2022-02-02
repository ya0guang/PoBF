#![cfg_attr(mirai, allow(incomplete_features), feature(generic_const_exprs))]

extern crate mirai_annotations;

use mirai_annotations::*;

#[cfg(mirai)]
use mirai_annotations::{TagPropagation, TagPropagationSet};

#[cfg(mirai)]
struct SecretTaintKind<const MASK: TagPropagationSet> {}

#[cfg(mirai)]
const SECRET_TAINT: TagPropagationSet = tag_propagation_set!(TagPropagation::SubComponent, TagPropagation::SuperComponent);

#[cfg(mirai)]
type SecretTaint = SecretTaintKind<SECRET_TAINT>;
#[cfg(not(mirai))]
type SecretTaint = ();

pub mod types;
use crate::types::*;

fn main() {
    let protected = ProtectedAssets::new(
        vec![0; 3],
        vec![0; 3],
        vec![0; 3],
    );
    add_tag!(&protected, SecretTaint);

    let protected = pre_function(protected);

    verify!(has_tag!(&protected, SecretTaint));

    let protected = exec_function(protected);
    verify!(has_tag!(&protected, SecretTaint));


    let _protected = post_function(protected);

    println!("terminated");
}

fn pre_function(x: ProtectedAssets<Encrypted, Input>) -> ProtectedAssets<Decrypted, Input> {
    precondition!(has_tag!(&x, SecretTaint));
    let y = x.decrypt();
    // let y = ProtectedAssets::new(
    //     vec![0; 3],
    //     vec![0; 3],
    //     vec![0; 3],
    // );
    // let y = y.decrypt();
    y
}

fn exec_function(x: ProtectedAssets<Decrypted, Input>) -> ProtectedAssets<Decrypted, Output> {
    assume!(has_tag!(&x, SecretTaint));

    let y = x.invoke(&foo);
    y
}

fn post_function(x: ProtectedAssets<Decrypted, Output>) -> ProtectedAssets<Encrypted, Output> {
    // precondition!(has_tag!(&x, SecretTaint));

    x.encrypt()
}

fn foo(_input: Vec<u8>) -> Vec<u8> {
    return vec![1; 3];
}
