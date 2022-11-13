#![cfg(feature = "mirai")]

use mirai_annotations::*;

#[cfg(feature = "mirai")]
use mirai_annotations::TagPropagationSet;
#[cfg(feature = "mirai")]
pub struct SecretTaintKind<const MASK: TagPropagationSet> {}
#[cfg(feature = "mirai")]
const SECRET_TAINT: TagPropagationSet = TAG_PROPAGATION_ALL;
#[cfg(feature = "mirai")]
pub type SecretTaint = SecretTaintKind<SECRET_TAINT>;

/// Ensures non-MIRAI code compiles.
#[cfg(not(feature = "mirai"))]
type SecretTaint = ();
