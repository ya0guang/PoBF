
#[cfg(mirai)]
use mirai_annotations::*;

#[cfg(mirai)]
pub struct SecretTaintKind<const MASK: TagPropagationSet> {}

#[cfg(mirai)]
const SECRET_TAINT: TagPropagationSet = TAG_PROPAGATION_ALL;

#[cfg(mirai)]
pub type SecretTaint = SecretTaintKind<SECRET_TAINT>;

