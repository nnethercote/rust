use rustc_middle::arena::Arena;
use rustc_middle::bug;
use rustc_middle::dep_graph::{DepKindVTable, DepNodeKey, KeyFingerprintStyle};
use rustc_middle::query::QueryCache;

use crate::GetQueryVTable;
use crate::plumbing::{force_from_dep_node_inner, try_load_from_on_disk_cache_inner};

/// [`DepKindVTable`] constructors for special dep kinds that aren't queries.
#[expect(non_snake_case, reason = "use non-snake case to avoid collision with query names")]
mod non_query {
    use super::*;

    // We use this for most things when incr. comp. is turned off.
    pub(crate) fn Null<'tcx>() -> DepKindVTable<'tcx> {
        DepKindVTable {
            is_anon: false,
            is_eval_always: false,
            key_fingerprint_style: KeyFingerprintStyle::Unit,
            force_from_dep_node: Some(|_, dep_node, _| {
                bug!("force_from_dep_node: encountered {dep_node:?}")
            }),
            try_load_from_on_disk_cache: None,
        }
    }

    // We use this for the forever-red node.
    pub(crate) fn Red<'tcx>() -> DepKindVTable<'tcx> {
        DepKindVTable {
            is_anon: false,
            is_eval_always: false,
            key_fingerprint_style: KeyFingerprintStyle::Unit,
            force_from_dep_node: Some(|_, dep_node, _| {
                bug!("force_from_dep_node: encountered {dep_node:?}")
            }),
            try_load_from_on_disk_cache: None,
        }
    }

    pub(crate) fn SideEffect<'tcx>() -> DepKindVTable<'tcx> {
        DepKindVTable {
            is_anon: false,
            is_eval_always: false,
            key_fingerprint_style: KeyFingerprintStyle::Unit,
            force_from_dep_node: Some(|tcx, _, prev_index| {
                tcx.dep_graph.force_diagnostic_node(tcx, prev_index);
                true
            }),
            try_load_from_on_disk_cache: None,
        }
    }

    pub(crate) fn AnonZeroDeps<'tcx>() -> DepKindVTable<'tcx> {
        DepKindVTable {
            is_anon: true,
            is_eval_always: false,
            key_fingerprint_style: KeyFingerprintStyle::Opaque,
            force_from_dep_node: Some(|_, _, _| bug!("cannot force an anon node")),
            try_load_from_on_disk_cache: None,
        }
    }

    pub(crate) fn TraitSelect<'tcx>() -> DepKindVTable<'tcx> {
        DepKindVTable {
            is_anon: true,
            is_eval_always: false,
            key_fingerprint_style: KeyFingerprintStyle::Unit,
            force_from_dep_node: None,
            try_load_from_on_disk_cache: None,
        }
    }

    pub(crate) fn CompileCodegenUnit<'tcx>() -> DepKindVTable<'tcx> {
        DepKindVTable {
            is_anon: false,
            is_eval_always: false,
            key_fingerprint_style: KeyFingerprintStyle::Opaque,
            force_from_dep_node: None,
            try_load_from_on_disk_cache: None,
        }
    }

    pub(crate) fn CompileMonoItem<'tcx>() -> DepKindVTable<'tcx> {
        DepKindVTable {
            is_anon: false,
            is_eval_always: false,
            key_fingerprint_style: KeyFingerprintStyle::Opaque,
            force_from_dep_node: None,
            try_load_from_on_disk_cache: None,
        }
    }

    pub(crate) fn Metadata<'tcx>() -> DepKindVTable<'tcx> {
        DepKindVTable {
            is_anon: false,
            is_eval_always: false,
            key_fingerprint_style: KeyFingerprintStyle::Unit,
            force_from_dep_node: None,
            try_load_from_on_disk_cache: None,
        }
    }
}

/// Shared implementation of the [`DepKindVTable`] constructor for queries.
/// Called from macro-generated code for each query.
pub(crate) fn make_dep_kind_vtable_for_query<'tcx, Q>(
    is_anon: bool,
    is_eval_always: bool,
) -> DepKindVTable<'tcx>
where
    Q: GetQueryVTable<'tcx>,
{
    let key_fingerprint_style = if is_anon {
        KeyFingerprintStyle::Opaque
    } else {
        <Q::Cache as QueryCache>::Key::key_fingerprint_style()
    };

    if is_anon || !key_fingerprint_style.reconstructible() {
        return DepKindVTable {
            is_anon,
            is_eval_always,
            key_fingerprint_style,
            force_from_dep_node: None,
            try_load_from_on_disk_cache: None,
        };
    }

    DepKindVTable {
        is_anon,
        is_eval_always,
        key_fingerprint_style,
        force_from_dep_node: Some(|tcx, dep_node, _| {
            force_from_dep_node_inner(Q::query_vtable(tcx), tcx, dep_node)
        }),
        try_load_from_on_disk_cache: Some(|tcx, dep_node| {
            try_load_from_on_disk_cache_inner(Q::query_vtable(tcx), tcx, dep_node)
        }),
    }
}

macro_rules! define_vtables {
    (
        queries {
            $(
                $(#[$attr:meta])*
                [$($modifiers:tt)*] fn $name:ident($K:ty) -> $V:ty,
            )*
        }
        non_queries {
            $(
                $(#[$nq_attr:meta])*
                $nq_name:ident,
            )*
        }
    ) => {
        // Create an array of vtables, one for each dep kind (non-query and query).
        pub fn make_dep_kind_vtables<'tcx>(arena: &'tcx Arena<'tcx>)
            -> &'tcx [DepKindVTable<'tcx>]
        {
            // The small number of non-query vtables: `Null`, `Red`, etc.
            let nq_vtables = [
                $(
                    non_query::$nq_name(),
                )*
            ];

            // The large number of query vtables.
            let q_vtables: [DepKindVTable<'tcx>; _] = [
                $(
                    $crate::dep_kind_vtables::make_dep_kind_vtable_for_query::<
                        $crate::query_impl::$name::VTableGetter,
                    >(
                        is_anon!([$($modifiers)*]),
                        is_eval_always!([$($modifiers)*]),
                    )
                ),*
            ];

            // Non-query vtables must come before query vtables, to match the order of `DepKind`.
            let iter = nq_vtables.into_iter().chain(q_vtables.into_iter());
            arena.alloc_from_iter(iter)
        }
    }
}

rustc_middle::rustc_with_all_queries! { define_vtables! }
