use crate::ty::{Lift, List, Ty, TyCtxt};
use rustc_hir as hir;
use rustc_errors::{DiagArgValue, IntoDiagArg};
use rustc_macros::{HashStable, TyDecodable, TyEncodable, TypeFoldable, TypeVisitable};
use rustc_target::spec::abi::Abi;
use rustc_type_ir::inherent::Tys;

// njn: derive Debug? or use the handwritten one?
#[derive(Clone, Copy, PartialEq, Eq, Hash, HashStable, TypeFoldable, TypeVisitable)]
#[derive(TyEncodable, TyDecodable)]
pub struct FnSig<'tcx> {
    pub inputs_and_output: &'tcx List<Ty<'tcx>>,
    pub c_variadic: bool,
    pub safety: hir::Safety,
    pub abi: Abi,
}

// njn: duplicates the `rustc_type_ir::inherent::FnSig` impl methods...
impl<'tcx> FnSig<'tcx> {
    pub fn inputs_and_output(self) -> &'tcx List<Ty<'tcx>> {
        self.inputs_and_output
    }

    pub fn inputs(self) -> &'tcx [Ty<'tcx>] {
        self.inputs_and_output.inputs()
    }

    pub fn output(self) -> Ty<'tcx> {
        self.inputs_and_output.output()
    }
}

// njn: can I auto-derive this somehow?
// njn: move?
impl<'a, 'tcx> Lift<TyCtxt<'tcx>> for FnSig<'a> {
    type Lifted = FnSig<'tcx>;

    fn lift_to_tcx(self, tcx: TyCtxt<'tcx>) -> Option<Self::Lifted> {
        Some(FnSig {
            inputs_and_output: self.inputs_and_output.lift_to_tcx(tcx)?,
            c_variadic: self.c_variadic,
            safety: self.safety,
            abi: self.abi,
        })
    }
}

// njn: move?
impl<'tcx> IntoDiagArg for FnSig<'tcx> {
    fn into_diag_arg(self) -> DiagArgValue {
        format!("{self:?}").into_diag_arg()
    }
}
