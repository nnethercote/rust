//use rustc_type_ir::Interner;
use crate::ty::{Ty, TyCtxt};

// njn: qual
#[derive(
    Clone,
    Copy,
    Debug,
    PartialEq,
    Eq,
    Hash,
    rustc_macros::HashStable,
    rustc_macros::TyEncodable,
    rustc_macros::TyDecodable,
    rustc_macros::TypeFoldable,
    rustc_macros::TypeVisitable
)]
// njn: visibilities?
pub struct Csa<'tcx> {
    pub inputs_and_output: &'tcx crate::ty::List<Ty<'tcx>>,
    pub c_variadic: bool,
    pub safety: rustc_hir::Safety,
    pub abi: rustc_target::spec::abi::Abi,
}

// njn: can I auto-derive this somehow?
impl<'a, 'tcx> crate::ty::Lift<TyCtxt<'tcx>> for Csa<'a> {
    type Lifted = Csa<'tcx>;

    fn lift_to_tcx(self, tcx: TyCtxt<'tcx>) -> Option<Self::Lifted> {
        let Csa { inputs_and_output, c_variadic, safety, abi } = self;
        Some(Csa {
            inputs_and_output: inputs_and_output.lift_to_tcx(tcx)?,
            c_variadic,
            safety,
            abi,
        })
    }
}
