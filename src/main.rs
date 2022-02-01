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
    verify!(does_not_have_tag!(&protected.data, SecretTaint));

    let protected = pre_function(protected);
    verify!(does_not_have_tag!(&protected, SecretTaint));
    let protected = exec_function(protected);

    let _protected = post_function(protected);
}

fn pre_function(x: ProtectedAssets<Encrypted, Input>) -> ProtectedAssets<Decrypted, Input> {
    precondition!(has_tag!(&x, SecretTaint));
    let y = x.decrypt();
    let y2 = ProtectedAssets::new(
        vec![0; 3],
        vec![0; 3],
        vec![0; 3],
    );
    let y3 = y2.decrypt();
    y3
}

fn exec_function(x: ProtectedAssets<Decrypted, Input>) -> ProtectedAssets<Decrypted, Output> {
    let y = x.invoke(&foo);
    y
}

fn post_function(x: ProtectedAssets<Decrypted, Output>) -> ProtectedAssets<Encrypted, Output> {
    x.encrypt()
}

fn foo(_input: Vec<u8>) -> Vec<u8> {
    return vec![1; 3];
}
