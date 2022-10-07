extern crate mirai_annotations;

use mirai_annotations::*;

pub struct SecretTaintKind<const MASK: TagPropagationSet> {}

const SECRET_TAINT: TagPropagationSet = TAG_PROPAGATION_ALL;

pub type SecretTaint = SecretTaintKind<SECRET_TAINT>;
