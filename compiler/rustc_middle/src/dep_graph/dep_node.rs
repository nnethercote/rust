use rustc_hir::def_id::DefId;
use rustc_hir::definitions::DefPathHash;
use rustc_query_system::dep_graph::dep_node::DepKind;
use rustc_query_system::dep_graph::{DepContext, DepNode, FingerprintStyle};
use rustc_span::Symbol;

use crate::mir::mono::MonoItem;
use crate::ty::TyCtxt;

macro_rules! define_dep_nodes {
    (
        $(
            $(#[$attr:meta])*
            [$($modifiers:tt)*] fn $variant:ident($($K:tt)*) -> $V:ty,
        )*
    ) => {
        #[macro_export]
        macro_rules! make_dep_kind_array {
            ($mod:ident) => {[ $($mod::$variant()),* ]};
        }

        #[allow(non_upper_case_globals)]
        pub mod dep_kinds {
            use super::*;

            $(
                pub const $variant: DepKind = DepKind::new(${index()});
            )*
        }

        // This checks that the discriminants of the variants have been assigned consecutively
        // from 0 so that they can be used as a dense index.
        pub(crate) const NUM_DEP_KIND_VARIANTS: u16 = ${count($variant)};

        /// List containing the name of each dep kind as a static string,
        /// indexable by `DepKind`.
        pub(crate) const DEP_KIND_NAMES: &[&str] = &[
            $( stringify!($variant), )*
        ];

        pub(super) fn dep_kind_from_label_string(label: &str) -> Result<DepKind, ()> {
            match label {
                $( stringify!($variant) => Ok(self::dep_kinds::$variant), )*
                _ => Err(()),
            }
        }

        /// Contains variant => str representations for constructing
        /// DepNode groups for tests.
        #[expect(non_upper_case_globals)]
        pub mod label_strs {
            $( pub const $variant: &str = stringify!($variant); )*
        }
    };
}

// Create various data structures for each query, and also for a few things
// that aren't queries.
rustc_with_all_queries!(define_dep_nodes![
    /// We use this for most things when incr. comp. is turned off.
    [] fn Null() -> (),
    /// We use this to create a forever-red node.
    [] fn Red() -> (),
    [] fn SideEffect() -> (),
    [] fn AnonZeroDeps() -> (),
    [] fn TraitSelect() -> (),
    [] fn CompileCodegenUnit() -> (),
    [] fn CompileMonoItem() -> (),
    [] fn Metadata() -> (),
]);

// WARNING: `construct` is generic and does not know that `CompileCodegenUnit` takes `Symbol`s as keys.
// Be very careful changing this type signature!
pub(crate) fn make_compile_codegen_unit(tcx: TyCtxt<'_>, name: Symbol) -> DepNode {
    DepNode::construct(tcx, dep_kinds::CompileCodegenUnit, &name)
}

// WARNING: `construct` is generic and does not know that `CompileMonoItem` takes `MonoItem`s as keys.
// Be very careful changing this type signature!
pub(crate) fn make_compile_mono_item<'tcx>(
    tcx: TyCtxt<'tcx>,
    mono_item: &MonoItem<'tcx>,
) -> DepNode {
    DepNode::construct(tcx, dep_kinds::CompileMonoItem, mono_item)
}

// WARNING: `construct` is generic and does not know that `Metadata` takes `()`s as keys.
// Be very careful changing this type signature!
pub(crate) fn make_metadata(tcx: TyCtxt<'_>) -> DepNode {
    DepNode::construct(tcx, dep_kinds::Metadata, &())
}

pub trait DepNodeExt: Sized {
    fn extract_def_id(&self, tcx: TyCtxt<'_>) -> Option<DefId>;

    fn from_label_string(
        tcx: TyCtxt<'_>,
        label: &str,
        def_path_hash: DefPathHash,
    ) -> Result<Self, ()>;

    fn has_label_string(label: &str) -> bool;
}

impl DepNodeExt for DepNode {
    /// Extracts the DefId corresponding to this DepNode. This will work
    /// if two conditions are met:
    ///
    /// 1. The Fingerprint of the DepNode actually is a DefPathHash, and
    /// 2. the item that the DefPath refers to exists in the current tcx.
    ///
    /// Condition (1) is determined by the DepKind variant of the
    /// DepNode. Condition (2) might not be fulfilled if a DepNode
    /// refers to something from the previous compilation session that
    /// has been removed.
    fn extract_def_id(&self, tcx: TyCtxt<'_>) -> Option<DefId> {
        if tcx.fingerprint_style(self.kind) == FingerprintStyle::DefPathHash {
            tcx.def_path_hash_to_def_id(DefPathHash(self.hash.into()))
        } else {
            None
        }
    }

    /// Used in testing
    fn from_label_string(
        tcx: TyCtxt<'_>,
        label: &str,
        def_path_hash: DefPathHash,
    ) -> Result<DepNode, ()> {
        let kind = dep_kind_from_label_string(label)?;

        match tcx.fingerprint_style(kind) {
            FingerprintStyle::Opaque | FingerprintStyle::HirId => Err(()),
            FingerprintStyle::Unit => Ok(DepNode::new_no_params(tcx, kind)),
            FingerprintStyle::DefPathHash => {
                Ok(DepNode::from_def_path_hash(tcx, def_path_hash, kind))
            }
        }
    }

    /// Used in testing
    fn has_label_string(label: &str) -> bool {
        dep_kind_from_label_string(label).is_ok()
    }
}

/// Maps a query label to its DepKind. Panics if a query with the given label does not exist.
pub fn dep_kind_from_label(label: &str) -> DepKind {
    dep_kind_from_label_string(label)
        .unwrap_or_else(|_| panic!("Query label {label} does not exist"))
}
