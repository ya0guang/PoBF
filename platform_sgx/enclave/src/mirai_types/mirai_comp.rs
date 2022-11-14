#![forbid(unsafe_code)]

#[cfg(mirai)]
use mirai_annotations::TagPropagationSet;
#[cfg(mirai)]
pub struct SecretTaintKind<const MASK: TagPropagationSet> {}
#[cfg(mirai)]
const SECRET_TAINT: TagPropagationSet = mirai_annotations::TAG_PROPAGATION_ALL;
#[cfg(mirai)]
pub type SecretTaint = SecretTaintKind<SECRET_TAINT>;
/// Ensures non-MIRAI code compiles.
#[cfg(not(mirai))]
pub type SecretTaint = ();
